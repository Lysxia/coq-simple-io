version_greater_equal()
{
  printf "%s\n%s\n" "$2" "$1" | sort --check=quiet --version-sort
}
COQ_VERSION=$(coqc --print-version|cut -d " " -f 1)

set -e

sh test.sh TestOcamlbuild
sh test.sh RunIO
sh test.sh HelloWorld
sh test.sh TestInt63 -r

# Testing separate extraction
sh test.sh Example -s
sh test.sh TestPervasives -s
sh test.sh TestExtraction -s
sh test.sh Argv -s
