/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2022 The Stockfish developers (see AUTHORS file)

  Stockfish is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Stockfish is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <cassert>

#include "movegen.h"
#include "position.h"

namespace Stockfish {

namespace {

  template<MoveType T>
  ExtMove* make_move_and_gating(const Position& pos, ExtMove* moveList, Color us, Square from, Square to, PieceType pt = NO_PIECE_TYPE) {

    // Wall placing moves
    //if it's "wall or move", and they chose non-null move, skip even generating wall move
    if (pos.walling() && !(pos.wall_or_move() && (from!=to)))
    {
        Bitboard b = pos.board_bb() & ~((pos.pieces() ^ from) | to);
        if (T == CASTLING)
        {
            Square kto = make_square(to > from ? pos.castling_kingside_file() : pos.castling_queenside_file(), pos.castling_rank(us));
            Direction step = kto > from ? EAST : WEST;
            Square rto = kto - step;
            b ^= square_bb(to) ^ kto ^ rto;
        }
        if (T == EN_PASSANT)
            b ^= pos.capture_square(to);

        if (pos.walling_rule() == ARROW)
            b &= moves_bb(us, type_of(pos.piece_on(from)), to, pos.pieces() ^ from);

        //Any current or future wall variant must follow the walling region rule if set:
        b &= pos.walling_region(us);

        if (pos.walling_rule() == PAST)
            b &= square_bb(from);
        if (pos.walling_rule() == EDGE)
        {
            Bitboard wallsquares = pos.state()->wallSquares;

            b &= (FileABB | file_bb(pos.max_file()) | Rank1BB | rank_bb(pos.max_rank())) |
               ( shift<NORTH     >(wallsquares) | shift<SOUTH     >(wallsquares)
               | shift<EAST      >(wallsquares) | shift<WEST      >(wallsquares));
        }
        while (b)
            *moveList++ = make_gating<T>(from, to, pt, pop_lsb(b));
        return moveList;
    }

    *moveList++ = make<T>(from, to, pt);

    // Gating moves
    if (pos.seirawan_gating() && (pos.gates(us) & from))
        for (PieceSet ps = pos.piece_types(); ps;)
        {
            PieceType pt_gating = pop_lsb(ps);
            if (pos.can_drop(us, pt_gating) && (pos.drop_region(us, pt_gating) & from))
                *moveList++ = make_gating<T>(from, to, pt_gating, from);
        }
    if (pos.seirawan_gating() && T == CASTLING && (pos.gates(us) & to))
        for (PieceSet ps = pos.piece_types(); ps;)
        {
            PieceType pt_gating = pop_lsb(ps);
            if (pos.can_drop(us, pt_gating) && (pos.drop_region(us, pt_gating) & to))
                *moveList++ = make_gating<T>(from, to, pt_gating, to);
        }

    return moveList;
  }

  template<Color c, GenType Type, Direction D>
  ExtMove* make_promotions(const Position& pos, ExtMove* moveList, Square to) {

    if (Type == CAPTURES || Type == EVASIONS || Type == NON_EVASIONS)
    {
        for (PieceSet promotions = pos.promotion_piece_types(c); promotions;)
        {
            PieceType pt = pop_msb(promotions);
            if (!pos.promotion_limit(pt) || pos.promotion_limit(pt) > pos.count(c, pt))
                moveList = make_move_and_gating<PROMOTION>(pos, moveList, pos.side_to_move(), to - D, to, pt);
        }
        PieceType pt = pos.promoted_piece_type(PAWN);
        if (pt && !(pos.piece_promotion_on_capture() && pos.empty(to)))
            moveList = make_move_and_gating<PIECE_PROMOTION>(pos, moveList, pos.side_to_move(), to - D, to);
    }

    return moveList;
  }

  template<Color Us, GenType Type>
  ExtMove* generate_drops(const Position& pos, ExtMove* moveList, PieceType pt, Bitboard b) {
    assert(Type != CAPTURES);
    // Do not generate virtual drops for perft and at root
    if (pos.can_drop(Us, pt) || (Type != NON_EVASIONS && pos.two_boards() && pos.allow_virtual_drop(Us, pt)))
    {
        // Restrict to valid target
        b &= pos.drop_region(Us, pt);

        // Add to move list
        if (pos.drop_promoted() && pos.promoted_piece_type(pt))
        {
            Bitboard b2 = b;
            if (Type == QUIET_CHECKS)
                b2 &= pos.check_squares(pos.promoted_piece_type(pt));
            while (b2)
                *moveList++ = make_drop(pop_lsb(b2), pt, pos.promoted_piece_type(pt));
        }
        if (Type == QUIET_CHECKS || !pos.can_drop(Us, pt))
            b &= pos.check_squares(pt);
        while (b)
            *moveList++ = make_drop(pop_lsb(b), pt, pt);
    }

    return moveList;
  }

  template<Color Us, GenType Type>
  ExtMove* generate_pawn_moves(const Position& pos, ExtMove* moveList, Bitboard target) {

    if (!pos.pieces(Us, PAWN))
        return moveList;

    constexpr Color     Them     = ~Us;
    constexpr Direction Up       = pawn_push(Us);
    constexpr Direction UpRight  = (Us == WHITE ? NORTH_EAST : SOUTH_WEST);
    constexpr Direction UpLeft   = (Us == WHITE ? NORTH_WEST : SOUTH_EAST);

    const Bitboard promotionZone = pos.promotion_zone(Us);
    const Bitboard standardPromotionZone = pos.sittuyin_promotion() ? Bitboard(0) : promotionZone;
    const Bitboard doubleStepRegion = pos.double_step_region(Us);
    const Bitboard tripleStepRegion = pos.triple_step_region(Us);

    const Bitboard pawns      = pos.pieces(Us, PAWN);
    const Bitboard movable    = pos.board_bb(Us, PAWN) & ~pos.pieces();
    const Bitboard capturable = pos.board_bb(Us, PAWN) &  pos.pieces(Them);

    target = Type == EVASIONS ? target : AllSquares;

    // Define single and double push, left and right capture, as well as respective promotion moves
    Bitboard b1 = shift<Up>(pawns) & movable & target;
    Bitboard b2 = shift<Up>(shift<Up>(pawns & doubleStepRegion) & movable) & movable & target;
    Bitboard b3 = shift<Up>(shift<Up>(shift<Up>(pawns & tripleStepRegion) & movable) & movable) & movable & target;
    Bitboard brc = shift<UpRight>(pawns) & capturable & target;
    Bitboard blc = shift<UpLeft >(pawns) & capturable & target;

    Bitboard b1p = b1 & standardPromotionZone;
    Bitboard b2p = b2 & standardPromotionZone;
    Bitboard b3p = b3 & standardPromotionZone;
    Bitboard brcp = brc & standardPromotionZone;
    Bitboard blcp = blc & standardPromotionZone;

    // Restrict regions based on rules and move generation type
    if (pos.mandatory_pawn_promotion())
    {
        b1 &= ~standardPromotionZone;
        b2 &= ~standardPromotionZone;
        b3 &= ~standardPromotionZone;
        brc &= ~standardPromotionZone;
        blc &= ~standardPromotionZone;
    }

    if (Type == QUIET_CHECKS && pos.count<KING>(Them))
    {
        // To make a quiet check, you either make a direct check by pushing a pawn
        // or push a blocker pawn that is not on the same file as the enemy king.
        // Discovered check promotion has been already generated amongst the captures.
        Square ksq = pos.square<KING>(Them);
        Bitboard dcCandidatePawns = pos.blockers_for_king(Them) & ~file_bb(ksq);
        b1 &= pawn_attacks_bb(Them, ksq) | shift<   Up>(dcCandidatePawns);
        b2 &= pawn_attacks_bb(Them, ksq) | shift<Up+Up>(dcCandidatePawns);
    }

    // Single and double pawn pushes, no promotions
    if (Type != CAPTURES)
    {
        while (b1)
        {
            Square to = pop_lsb(b1);
            moveList = make_move_and_gating<NORMAL>(pos, moveList, Us, to - Up, to);
        }

        while (b2)
        {
            Square to = pop_lsb(b2);
            moveList = make_move_and_gating<NORMAL>(pos, moveList, Us, to - Up - Up, to);
        }

        while (b3)
        {
            Square to = pop_lsb(b3);
            moveList = make_move_and_gating<NORMAL>(pos, moveList, Us, to - Up - Up - Up, to);
        }
    }

    // Promotions and underpromotions
    while (brcp)
        moveList = make_promotions<Us, Type, UpRight>(pos, moveList, pop_lsb(brcp));

    while (blcp)
        moveList = make_promotions<Us, Type, UpLeft >(pos, moveList, pop_lsb(blcp));

    while (b1p)
        moveList = make_promotions<Us, Type, Up     >(pos, moveList, pop_lsb(b1p));

    while (b2p)
        moveList = make_promotions<Us, Type, Up+Up  >(pos, moveList, pop_lsb(b2p));

    while (b3p)
        moveList = make_promotions<Us, Type, Up+Up+Up>(pos, moveList, pop_lsb(b3p));

    // Sittuyin promotions
    if (pos.sittuyin_promotion() && (Type == CAPTURES || Type == EVASIONS || Type == NON_EVASIONS))
    {
        // Pawns need to be in promotion zone if there is more than one pawn
        Bitboard promotionPawns = pos.count<PAWN>(Us) > 1 ? pawns & promotionZone : pawns;
        while (promotionPawns)
        {
            Square from = pop_lsb(promotionPawns);
            for (PieceSet ps = pos.promotion_piece_types(Us); ps;)
            {
                PieceType pt = pop_msb(ps);
                if (pos.promotion_limit(pt) && pos.promotion_limit(pt) <= pos.count(Us, pt))
                    continue;
                Bitboard b = ((pos.attacks_from(Us, pt, from) & ~pos.pieces()) | from) & target;
                while (b)
                {
                    Square to = pop_lsb(b);
                    if (!(attacks_bb(Us, pt, to, pos.pieces() ^ from) & pos.pieces(Them)))
                        *moveList++ = make<PROMOTION>(from, to, pt);
                }
            }
        }
    }

    // Standard and en passant captures
    if (Type == CAPTURES || Type == EVASIONS || Type == NON_EVASIONS)
    {
        while (brc)
        {
            Square to = pop_lsb(brc);
            moveList = make_move_and_gating<NORMAL>(pos, moveList, Us, to - UpRight, to);
        }

        while (blc)
        {
            Square to = pop_lsb(blc);
            moveList = make_move_and_gating<NORMAL>(pos, moveList, Us, to - UpLeft, to);
        }

        for (Bitboard epSquares = pos.ep_squares() & ~pos.pieces(); epSquares; )
        {
            Square epSquare = pop_lsb(epSquares);

            // An en passant capture cannot resolve a discovered check (unless there non-sliding riders)
            if (Type == EVASIONS && (target & (epSquare + Up)) && !pos.non_sliding_riders())
                return moveList;

            Bitboard b = pawns & pawn_attacks_bb(Them, epSquare);

            // En passant square is already disabled for non-fairy variants if there is no attacker
            assert(b || !pos.fast_attacks());

            while (b)
                moveList = make_move_and_gating<EN_PASSANT>(pos, moveList, Us, pop_lsb(b), epSquare);
        }
    }

    return moveList;
  }


  template<Color Us, GenType Type>
  ExtMove* generate_moves(const Position& pos, ExtMove* moveList, PieceType Pt, Bitboard target) {

    assert(Pt != KING && Pt != PAWN);

    Bitboard bb = pos.pieces(Us, Pt);

    while (bb)
    {
        Square from = pop_lsb(bb);

        Bitboard attacks = pos.attacks_from(Us, Pt, from);
        Bitboard quiets = pos.moves_from(Us, Pt, from);
        Bitboard b = (  (attacks & pos.pieces())
                       | (quiets & ~pos.pieces()));
        Bitboard b1 = b & target;
        Bitboard promotion_zone = pos.promotion_zone(Us);
        PieceType promPt = pos.promoted_piece_type(Pt);
        Bitboard b2 = promPt && (!pos.promotion_limit(promPt) || pos.promotion_limit(promPt) > pos.count(Us, promPt)) ? b1 : Bitboard(0);
        Bitboard b3 = pos.piece_demotion() && pos.is_promoted(from) ? b1 : Bitboard(0);
        Bitboard pawnPromotions = (pos.promotion_pawn_types(Us) & Pt) ? (b & (Type == EVASIONS ? target : ~pos.pieces(Us)) & promotion_zone) : Bitboard(0);
        Bitboard epSquares = (pos.en_passant_types(Us) & Pt) ? (attacks & ~quiets & pos.ep_squares() & ~pos.pieces()) : Bitboard(0);

        // target squares considering pawn promotions
        if (pawnPromotions && pos.mandatory_pawn_promotion())
            b1 &= ~pawnPromotions;

        // Restrict target squares considering promotion zone
        if (b2 | b3)
        {
            if (pos.mandatory_piece_promotion())
                b1 &= (promotion_zone & from ? Bitboard(0) : ~promotion_zone) | (pos.piece_promotion_on_capture() ? ~pos.pieces() : Bitboard(0));
            // Exclude quiet promotions/demotions
            if (pos.piece_promotion_on_capture())
            {
                b2 &= pos.pieces();
                b3 &= pos.pieces();
            }
            // Consider promotions/demotions into promotion zone
            if (!(promotion_zone & from))
            {
                b2 &= promotion_zone;
                b3 &= promotion_zone;
            }
        }

        if (Type == QUIET_CHECKS)
        {
            b1 &= pos.check_squares(Pt);
            if (b2)
                b2 &= pos.check_squares(pos.promoted_piece_type(Pt));
            if (b3)
                b3 &= pos.check_squares(type_of(pos.unpromoted_piece_on(from)));
        }

        while (b1)
            moveList = make_move_and_gating<NORMAL>(pos, moveList, Us, from, pop_lsb(b1));

        // Shogi-style piece promotions
        while (b2)
            *moveList++ = make<PIECE_PROMOTION>(from, pop_lsb(b2));

        // Piece demotions
        while (b3)
            *moveList++ = make<PIECE_DEMOTION>(from, pop_lsb(b3));

        // Pawn-style promotions
        if ((Type == CAPTURES || Type == EVASIONS || Type == NON_EVASIONS) && pawnPromotions)
            for (PieceSet ps = pos.promotion_piece_types(Us); ps;)
            {
                PieceType ptP = pop_msb(ps);
                if (!pos.promotion_limit(ptP) || pos.promotion_limit(ptP) > pos.count(Us, ptP))
                    for (Bitboard promotions = pawnPromotions; promotions; )
                        moveList = make_move_and_gating<PROMOTION>(pos, moveList, pos.side_to_move(), from, pop_lsb(promotions), ptP);
            }

        // En passant captures
        if (Type == CAPTURES || Type == EVASIONS || Type == NON_EVASIONS)
            while (epSquares)
                moveList = make_move_and_gating<EN_PASSANT>(pos, moveList, Us, from, pop_lsb(epSquares));
    }

    return moveList;
  }


  template<Color Us, GenType Type>
  ExtMove* generate_all(const Position& pos, ExtMove* moveList) {

    static_assert(Type != LEGAL, "Unsupported type in generate_all()");

    constexpr bool Checks = Type == QUIET_CHECKS; // Reduce template instantiations
    const Square ksq = pos.count<KING>(Us) ? pos.square<KING>(Us) : SQ_NONE;
    Bitboard target;

    // Skip generating non-king moves when in double check
    if (Type != EVASIONS || !more_than_one(pos.checkers() & ~pos.non_sliding_riders()))
    {
        target = Type == EVASIONS     ?  between_bb(ksq, lsb(pos.checkers()))
               : Type == NON_EVASIONS ? ~pos.pieces( Us)
               : Type == CAPTURES     ?  pos.pieces(~Us)
                                      : ~pos.pieces(   ); // QUIETS || QUIET_CHECKS

        if (Type == EVASIONS)
        {
            if (pos.checkers() & pos.non_sliding_riders())
                target = ~pos.pieces(Us);
            // Leaper attacks can not be blocked
            Square checksq = lsb(pos.checkers());
            if (LeaperAttacks[~Us][type_of(pos.piece_on(checksq))][checksq] & pos.square<KING>(Us))
                target = pos.checkers();
        }

        // Remove inaccessible squares (outside board + wall squares)
        target &= pos.board_bb();

        moveList = generate_pawn_moves<Us, Type>(pos, moveList, target);
        for (PieceSet ps = pos.piece_types() & ~(piece_set(PAWN) | KING); ps;)
            moveList = generate_moves<Us, Type>(pos, moveList, pop_lsb(ps), target);
        // generate drops
        if (pos.piece_drops() && Type != CAPTURES && (pos.can_drop(Us, ALL_PIECES) || pos.two_boards()))
            for (PieceSet ps = pos.piece_types(); ps;)
                moveList = generate_drops<Us, Type>(pos, moveList, pop_lsb(ps), target & ~pos.pieces(~Us));

        // Castling with non-king piece
        if (!pos.count<KING>(Us) && Type != CAPTURES && pos.can_castle(Us & ANY_CASTLING))
        {
            Square from = pos.castling_king_square(Us);
            for(CastlingRights cr : { Us & KING_SIDE, Us & QUEEN_SIDE } )
                if (!pos.castling_impeded(cr) && pos.can_castle(cr))
                    moveList = make_move_and_gating<CASTLING>(pos, moveList, Us, from, pos.castling_rook_square(cr));
        }

        // Special moves
        if (pos.cambodian_moves() && pos.gates(Us) && Type != CAPTURES)
        {
            if (Type != EVASIONS && (pos.pieces(Us, KING) & pos.gates(Us)))
            {
                Square from = pos.square<KING>(Us);
                Bitboard b = PseudoAttacks[WHITE][KNIGHT][from] & rank_bb(rank_of(from + (Us == WHITE ? NORTH : SOUTH)))
                    & target & ~pos.pieces();
                while (b)
                    moveList = make_move_and_gating<SPECIAL>(pos, moveList, Us, from, pop_lsb(b));
            }

            Bitboard b = pos.pieces(Us, FERS) & pos.gates(Us);
            while (b)
            {
                Square from = pop_lsb(b);
                Square to = from + 2 * (Us == WHITE ? NORTH : SOUTH);
                if (is_ok(to) && (target & to & ~pos.pieces()))
                    moveList = make_move_and_gating<SPECIAL>(pos, moveList, Us, from, to);
            }
        }

        // Workaround for passing: Execute a non-move with any piece
        if (pos.pass(Us) && !pos.count<KING>(Us) && pos.pieces(Us))
            *moveList++ = make<SPECIAL>(lsb(pos.pieces(Us)), lsb(pos.pieces(Us)));

        //if "wall or move", generate walling action with null move
        if (pos.wall_or_move())
        {
            moveList = make_move_and_gating<SPECIAL>(pos, moveList, Us, lsb(pos.pieces(Us)), lsb(pos.pieces(Us)));
        }
    }

    // King moves
    if (pos.count<KING>(Us) && (!Checks || pos.blockers_for_king(~Us) & ksq))
    {
        Bitboard b = (  (pos.attacks_from(Us, KING, ksq) & pos.pieces())
                      | (pos.moves_from(Us, KING, ksq) & ~pos.pieces())) & (Type == EVASIONS ? ~pos.pieces(Us) : target);
        while (b)
            moveList = make_move_and_gating<NORMAL>(pos, moveList, Us, ksq, pop_lsb(b));

        // Passing move by king
        if (pos.pass(Us))
            *moveList++ = make<SPECIAL>(ksq, ksq);

        if ((Type == QUIETS || Type == NON_EVASIONS) && pos.can_castle(Us & ANY_CASTLING))
            for (CastlingRights cr : { Us & KING_SIDE, Us & QUEEN_SIDE } )
                if (!pos.castling_impeded(cr) && pos.can_castle(cr))
                    moveList = make_move_and_gating<CASTLING>(pos, moveList, Us,ksq, pos.castling_rook_square(cr));
    }

    // Wizard swap moves
    {
        std::string ptc = pos.piece_to_char();
        std::size_t widx = ptc.find('W');
        if (widx != std::string::npos) {
            Piece white_wizard = Piece(widx);
            Piece black_wizard = Piece(ptc.find('w'));
            Piece our_wizard = (Us == WHITE) ? white_wizard : black_wizard;
            Bitboard wizards = pos.pieces(Us);
            while (wizards) {
                Square from = pop_lsb(wizards);
                if (pos.piece_on(from) != our_wizard)
                    continue;
                Bitboard attacks = pos.attacks_from(Us, type_of(our_wizard), from);
                Bitboard quiets  = pos.moves_from(Us, type_of(our_wizard), from);
                Bitboard reachable = attacks | quiets;
                Bitboard swapTargets = reachable & pos.pieces(Us) & ~square_bb(from);
                while (swapTargets) {
                    Square target = pop_lsb(swapTargets);
                    // Wizard on back rank swapping with a pawn: pawn lands on back rank and promotes
                    if (   type_of(pos.piece_on(target)) == PAWN
                        && relative_rank(Us, from, pos.max_rank()) == pos.max_rank())
                    {
                        for (PieceSet ps = pos.promotion_piece_types(Us); ps; )
                        {
                            PieceType pt = pop_msb(ps);
                            if (!pos.promotion_limit(pt) || pos.promotion_limit(pt) > pos.count(Us, pt))
                                *moveList++ = make<SWAP_PROMOTION>(from, target, pt);
                        }
                    }
                    else
                        *moveList++ = make<SWAP>(from, target);
                }
            }
        }
    }

    // Archer ranged captures
{

    std::string ptc = pos.piece_to_char();
    std::size_t xidx = ptc.find('X');
    if (xidx != std::string::npos) {
        Piece white_archer = Piece(xidx);
        Piece black_archer = Piece(ptc.find('x'));
        Piece our_archer = (Us == WHITE) ? white_archer : black_archer;
        Bitboard archers = pos.pieces(Us);
        int archer_count = 0;
        while (archers) {
            Square from = pop_lsb(archers);
            if (pos.piece_on(from) != our_archer)
                continue;
            archer_count++;
            // Check all 4 diagonal directions, 2 and 3 squares out
            for (Direction d : {NORTH_EAST, NORTH_WEST, SOUTH_EAST, SOUTH_WEST}) {
                for (int dist = 2; dist <= 3; dist++) {
                    Square target = from;
                    bool valid = true;
                    for (int step = 0; step < dist; step++) {
                        // bounds check
                        File f = file_of(target);
                        Rank r = rank_of(target);
                        if (   (d == NORTH_EAST && (f == FILE_H || r == RANK_8))
                            || (d == NORTH_WEST && (f == FILE_A || r == RANK_8))
                            || (d == SOUTH_EAST && (f == FILE_H || r == RANK_1))
                            || (d == SOUTH_WEST && (f == FILE_A || r == RANK_1))) {
                            valid = false;
                            break;
                        }
                        target = target + d;
                    }
                    if (!valid) break;
                    // Only generate if target has an enemy piece
                    if (pos.pieces(~Us) & square_bb(target))
                        *moveList++ = make_archer_shot(from, target);
                }
            }
        }
    }
}

    // Painter: forward non-capturing moves + diagonal paint moves
    {
        std::string ptc = pos.piece_to_char();
        std::size_t yidx = ptc.find('Y');
        if (yidx != std::string::npos) {
            Piece white_painter = Piece(yidx);
            Piece black_painter = Piece(ptc.find('y'));
            Piece our_painter   = (Us == WHITE) ? white_painter : black_painter;

            // Royal painter type for back-rank promotion
            std::size_t oidx = ptc.find('O');
            PieceType royalPainterType = oidx != std::string::npos ? type_of(Piece(oidx)) : NO_PIECE_TYPE;

            Direction forward     = (Us == WHITE) ? NORTH      : SOUTH;
            Direction paintLeft   = (Us == WHITE) ? NORTH_WEST : SOUTH_EAST;
            Direction paintRight  = (Us == WHITE) ? NORTH_EAST : SOUTH_WEST;
            Rank      startRank   = (Us == WHITE) ? RANK_2     : RANK_7;

            // Wet paint square: the piece here cannot be painted this ply
            Square wetSq = pos.state()->wetPaintSquare;

            Bitboard painters = pos.pieces(Us);
            while (painters) {
                Square from = pop_lsb(painters);
                if (pos.piece_on(from) != our_painter)
                    continue;

                // --- Forward non-capturing moves ---
                Square one = from + forward;
                if (is_ok(one) && pos.empty(one)) {
                    if (Type != CAPTURES) {
                        // Back-rank arrival → promote to royal painter
                        if (royalPainterType != NO_PIECE_TYPE
                            && relative_rank(Us, one, pos.max_rank()) == pos.max_rank())
                            *moveList++ = make<PROMOTION>(from, one, royalPainterType);
                        else
                            *moveList++ = make_move(from, one);
                    }
                    // Initial double push (never reaches back rank directly)
                    if (rank_of(from) == startRank) {
                        Square two = one + forward;
                        if (is_ok(two) && pos.empty(two) && Type != CAPTURES)
                            *moveList++ = make_move(from, two);
                    }
                }

                // --- Paint moves (diagonal, like pawn captures) ---
                for (Direction d : {paintLeft, paintRight}) {
                    // Guard against file wrap-around
                    File f = file_of(from);
                    if (d == NORTH_WEST && f == FILE_A) continue;
                    if (d == NORTH_EAST && f == FILE_H) continue;
                    if (d == SOUTH_WEST && f == FILE_A) continue;
                    if (d == SOUTH_EAST && f == FILE_H) continue;
                    Square target = from + d;
                    if (!is_ok(target))
                        continue;

                    // Normal paint: enemy piece on target (not king, not wet paint)
                    if ((pos.pieces(~Us) & square_bb(target))
                        && type_of(pos.piece_on(target)) != KING
                        && target != wetSq)
                        *moveList++ = make<PAINTER_PAINT>(from, target);

                    // En passant paint: target is the ep square (empty)
                    if (pos.ep_squares() & square_bb(target)) {
                        Square epTarget = pos.capture_square(target);
                        if (epTarget != wetSq
                            && type_of(pos.piece_on(epTarget)) != KING)
                            *moveList++ = make<PAINTER_PAINT>(from, target);
                    }
                }
            }
        }
    }

    // Snare promotion: when snare reaches the back rank it becomes a rolling snare
    if (Type != CAPTURES)
    {
        std::string ptc = pos.piece_to_char();
        std::size_t sidx = ptc.find('S');
        std::size_t lidx = ptc.find('L');
        if (sidx != std::string::npos && lidx != std::string::npos) {
            Piece white_snare = Piece(sidx);
            Piece black_snare = Piece(ptc.find('s'));
            Piece our_snare   = (Us == WHITE) ? white_snare : black_snare;
            PieceType rollingSnareType = type_of(Piece(lidx));

            Bitboard snares = pos.pieces(Us);
            while (snares) {
                Square from = pop_lsb(snares);
                if (pos.piece_on(from) != our_snare)
                    continue;
                // All squares the snare can move to (from its Betza)
                Bitboard dests = pos.moves_from(Us, type_of(our_snare), from)
                                 & ~pos.pieces()
                                 & pos.board_bb();
                while (dests) {
                    Square to = pop_lsb(dests);
                    if (relative_rank(Us, to, pos.max_rank()) == pos.max_rank())
                        *moveList++ = make<PROMOTION>(from, to, rollingSnareType);
                }
            }
        }
    }

    // Royal Painter: queen-range paint moves (piece stays at 'from'; target becomes our color)
    {
        std::string ptc = pos.piece_to_char();
        std::size_t oidx = ptc.find('O');
        if (oidx != std::string::npos) {
            Piece white_rp = Piece(oidx);
            Piece black_rp = Piece(ptc.find('o'));
            Piece our_rp   = (Us == WHITE) ? white_rp : black_rp;
            Square wetSq   = pos.state()->wetPaintSquare;
            Bitboard rps   = pos.pieces(Us);
            while (rps) {
                Square from = pop_lsb(rps);
                if (pos.piece_on(from) != our_rp)
                    continue;
                // Enemy pieces visible along queen rays (blocking by any piece applies)
                Bitboard paintTargets = attacks_bb(Us, QUEEN, from, pos.pieces())
                                        & pos.pieces(~Us)
                                        & ~pos.pieces(~Us, KING);
                if (wetSq != SQ_NONE)
                    paintTargets &= ~square_bb(wetSq);
                while (paintTargets) {
                    Square target = pop_lsb(paintTargets);
                    *moveList++ = make<PAINTER_PAINT>(from, target);
                }
            }
        }
    }

    return moveList;
  }

} // namespace


/// <CAPTURES>     Generates all pseudo-legal captures plus queen promotions
/// <QUIETS>       Generates all pseudo-legal non-captures and underpromotions
/// <EVASIONS>     Generates all pseudo-legal check evasions when the side to move is in check
/// <QUIET_CHECKS> Generates all pseudo-legal non-captures giving check, except castling and promotions
/// <NON_EVASIONS> Generates all pseudo-legal captures and non-captures
///
/// Returns a pointer to the end of the move list.

template<GenType Type>
ExtMove* generate(const Position& pos, ExtMove* moveList) {

  static_assert(Type != LEGAL, "Unsupported type in generate()");
  assert((Type == EVASIONS) == (bool)pos.checkers());

  Color us = pos.side_to_move();

  return us == WHITE ? generate_all<WHITE, Type>(pos, moveList)
                     : generate_all<BLACK, Type>(pos, moveList);
}

// Explicit template instantiations
template ExtMove* generate<CAPTURES>(const Position&, ExtMove*);
template ExtMove* generate<QUIETS>(const Position&, ExtMove*);
template ExtMove* generate<EVASIONS>(const Position&, ExtMove*);
template ExtMove* generate<QUIET_CHECKS>(const Position&, ExtMove*);
template ExtMove* generate<NON_EVASIONS>(const Position&, ExtMove*);


/// generate<LEGAL> generates all the legal moves in the given position

template<>
ExtMove* generate<LEGAL>(const Position& pos, ExtMove* moveList) {
  if (pos.is_immediate_game_end())
      return moveList;

  // Get snare piece type for this variant
  PieceType snare_type = NO_PIECE_TYPE;
  std::string ptc = pos.piece_to_char();
  std::size_t idx_white = ptc.find('S');
  std::size_t idx_black = ptc.find('s');
// Instead of computing make_piece, just compare Piece directly
Piece white_snare = idx_white != std::string::npos ? Piece(idx_white) : NO_PIECE;
Piece black_snare = idx_black != std::string::npos ? Piece(idx_black) : NO_PIECE;
  std::size_t idx_rs_white = ptc.find('L');
  std::size_t idx_rs_black = ptc.find('l');
Piece white_rolling_snare = idx_rs_white != std::string::npos ? Piece(idx_rs_white) : NO_PIECE;
Piece black_rolling_snare = idx_rs_black != std::string::npos ? Piece(idx_rs_black) : NO_PIECE;

  ExtMove* cur = moveList;
  moveList = pos.checkers() ? generate<EVASIONS    >(pos, moveList)
                            : generate<NON_EVASIONS>(pos, moveList);
  while (cur != moveList) {
      if (!pos.legal(*cur) || pos.virtual_drop(*cur)) {
          *cur = (--moveList)->move;
          continue;
      }

      // Snare immobilization check
      if (white_snare != NO_PIECE || black_snare != NO_PIECE) {
          Square from = from_sq(*cur);
          Color us = color_of(pos.piece_on(from));
          Color them = ~us;
          Piece enemy_snare = (us == WHITE) ? black_snare : white_snare;
          Direction forward = (us == WHITE) ? NORTH : SOUTH;
          File from_file = file_of(from);
          Rank from_rank = rank_of(from);

          bool immobilized = false;

          if (enemy_snare!= NO_PIECE){

          // Check WEST (left)
          if (from_file > FILE_A) {
              Square adj = from + WEST;
              if (pos.piece_on(adj) == enemy_snare)
                immobilized = true;
          }
          // Check EAST (right)
          if (!immobilized && from_file < FILE_H) {
              Square adj = from + EAST;
              if (pos.piece_on(adj) == enemy_snare)
                immobilized = true;
          }
          // Check forward
          if (!immobilized) {
              Rank fwd_rank = (us == WHITE) ? Rank(from_rank + 1) : Rank(from_rank - 1);
              if (fwd_rank >= RANK_1 && fwd_rank <= RANK_8) {
                  Square adj = from + forward;
                  if (pos.piece_on(adj) == enemy_snare)
                    immobilized = true;
              }
          }
        }

          if (immobilized) {
              *cur = (--moveList)->move;
              continue;
          }
      }

      // Rolling snare immobilization check (immobilizes all 4 orthogonal neighbors)
      if (white_rolling_snare != NO_PIECE || black_rolling_snare != NO_PIECE) {
          Square from = from_sq(*cur);
          Color us = color_of(pos.piece_on(from));
          Piece enemy_rs = (us == WHITE) ? black_rolling_snare : white_rolling_snare;

          if (enemy_rs != NO_PIECE) {
              File from_file = file_of(from);
              Rank from_rank = rank_of(from);
              bool immobilized = false;
              if (!immobilized && from_file > FILE_A && pos.piece_on(from + WEST)  == enemy_rs) immobilized = true;
              if (!immobilized && from_file < FILE_H && pos.piece_on(from + EAST)  == enemy_rs) immobilized = true;
              if (!immobilized && from_rank < RANK_8  && pos.piece_on(from + NORTH) == enemy_rs) immobilized = true;
              if (!immobilized && from_rank > RANK_1  && pos.piece_on(from + SOUTH) == enemy_rs) immobilized = true;
              if (immobilized) {
                  *cur = (--moveList)->move;
                  continue;
              }
          }
      }

      ++cur;
  }
  return moveList;
}

} // namespace Stockfish
