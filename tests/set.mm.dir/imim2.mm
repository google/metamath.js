include "wi.mm";
include "id.mm";
include "imim2d.mm";

theorem imim2(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {





  do {
    wph;
    wps;
    wi;
    #;
    wph;
    wps;
    wch;
    @0;
    id;
    imim2d;
  };

  return '|-' "( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) )";
}
