include "id.mm";
include "nsyl3.mm";

theorem con2i(wph: 'wff' ph, wps: 'wff' ps) {
  assume con2i.a: |- "( ph -> -. ps )";





  do {
    wph;
    wps;
    wps;
    con2i.a;
    wps;
    id;
    nsyl3;
  };

  return '|-' "( ps -> -. ph )";
}
