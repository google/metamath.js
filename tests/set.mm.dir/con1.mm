include "wn.mm";
include "wi.mm";
include "id.mm";
include "con1d.mm";

theorem con1(wph: 'wff' ph, wps: 'wff' ps) {





  do {
    wph;
    wn;
    wps;
    wi;
    #;
    wph;
    wps;
    @0;
    id;
    con1d;
  };

  return '|-' "( ( -. ph -> ps ) -> ( -. ps -> ph ) )";
}
