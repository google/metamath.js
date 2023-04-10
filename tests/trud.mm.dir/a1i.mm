include "kt.mm";
include "ax-trud.mm";
include "syl.mm";

theorem a1i(ta: $term$ A, tr: $term$ R) {
  assume ax-trud.1: $|- R : bool$;
  assume ax-a1i.2: $|- T. |= A$;





  do {
    tr;
    kt;
    ta;
    tr;
    ax-trud.1;
    ax-trud;
    ax-a1i.2;
    syl;
  };

  return $|- R |= A$;
}
