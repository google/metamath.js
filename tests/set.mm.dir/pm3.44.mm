include "wi.mm";
include "id.mm";
include "jaao.mm";

theorem pm3.44(wph: wff ph, wps: wff ps, wch: wff ch) {





  do {
    wps;
    wph;
    wi;
    #;
    wps;
    wph;
    wch;
    wph;
    wi;
    #;
    wch;
    @0;
    id;
    @1;
    id;
    jaao;
  };

  return |- "( ( ( ps -> ph ) /\\ ( ch -> ph ) ) -> ( ( ps \\/ ch ) -> ph ) )";
}
