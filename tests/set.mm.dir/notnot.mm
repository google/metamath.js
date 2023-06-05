include "wn.mm";
include "id.mm";
include "con2i.mm";

theorem notnot(wph: wff ph) {





  do {
    wph;
    wn;
    #;
    wph;
    @0;
    id;
    con2i;
  };

  return |- "( ph -> -. -. ph )";
}
