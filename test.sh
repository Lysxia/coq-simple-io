COQ_OPTS="-I ../plugin/ -Q ../src/ SimpleIO"
case $2 in
  -i)
    COQ_OPTS=$3
    ;;
  *)
    ;;
esac

mkdir -p build/

cd build/
coqc $COQ_OPTS ../test/$1.v
case $2 in
  -n)
     ;;
  *)
   rm *.mli
   ocamlbuild -lib unix $1.native
   ./$1.native
esac
