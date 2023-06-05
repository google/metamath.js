include "wn.mm";
include "id.mm";
include "nsyl2.mm";

theorem con1i(wph: wff ph, wps: wff ps) {
  assume con1i.1: |- "( -. ph -> ps )";





  do {
    wps;
    wn;
    #;
    wps;
    wph;
    @0;
    id;
    con1i.1;
    nsyl2;
  };

  return |- "( -. ps -> ph )";
}
