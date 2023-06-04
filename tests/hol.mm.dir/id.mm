include "ax-id.mm";

theorem id(tr: term R) {
  assume ax-id.1: |- "R : bool";





  do {
    tr;
    ax-id.1;
    ax-id;
  };

  return '|-' "R |= R";
}
