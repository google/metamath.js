include "wn.mm";
include "id.mm";
include "nsyl.mm";

theorem con3i(wph: 'wff' ph, wps: 'wff' ps) {
  assume con3i.a: |- "( ph -> ps )";





  do {
    wps;
    wn;
    #;
    wps;
    wph;
    @0;
    id;
    con3i.a;
    nsyl;
  };

  return '|-' "( -. ps -> -. ph )";
}
