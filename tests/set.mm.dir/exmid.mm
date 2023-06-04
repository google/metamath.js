include "wn.mm";
include "id.mm";
include "orri.mm";

theorem exmid(wph: 'wff' ph) {





  do {
    wph;
    wph;
    wn;
    #;
    @0;
    id;
    orri;
  };

  return '|-' "( ph \\/ -. ph )";
}
