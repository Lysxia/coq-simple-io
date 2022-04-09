set -e
echo "Testing" $1 "..."

mkdir -p build/

cd build/
coqc ../test/$1.v
case $2 in
  -s)
    rm *.mli
    ocamlbuild -lib unix $1.native
    ./$1.native
    ;;
  *)
    ;;
esac
