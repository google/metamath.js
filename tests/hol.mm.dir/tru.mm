include "kt.mm";
include "wtru.mm";
include "id.mm";

theorem tru() {





  do {
    kt;
    wtru;
    id;
  };

  return $|-$ $T. |= T.$;
}
