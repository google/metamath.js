include "ax-trud.mm";

theorem trud(tr: 'term' R) {
  assume ax-trud.1: |- "R : bool";





  do {
    tr;
    ax-trud.1;
    ax-trud;
  };

  return '|-' "R |= T.";
}
