set -e
echo "Testing" $1 "..."

mkdir -p build/

cd build/
coqc ../test/$1.v > $1.out
case $2 in
  -s)
    rm *.mli
    ocamlbuild -use-ocamlfind -lib unix $1.native
    ./$1.native
    ;;
  -r)
    diff -q ../test/$1.ref $1.out
    ;;
  *)
    ;;
esac
