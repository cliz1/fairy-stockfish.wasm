#!/bin/bash
set -e

echo "Building..."
cd src/emscripten
DOCKER_USER=$(id -u):$(id -g) docker-compose run --rm emscripten bash -c "make -C .. ARCH=wasm emscripten_clean"
DOCKER_USER=$(id -u):$(id -g) docker-compose run --rm emscripten bash -c "make -C .. emscripten_build ARCH=wasm embedded_nnue=no"
cd ../..

echo "Copying files..."
cp src/emscripten/public/stockfish.js ../tokenchess/public/
cp src/emscripten/public/stockfish.wasm ../tokenchess/public/
cp src/emscripten/public/stockfish.worker.js ../tokenchess/public/

echo "Done."