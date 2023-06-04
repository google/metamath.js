include "wi.mm";
include "biimprd.mm";
include "imim1d.mm";
include "biimpd.mm";
include "impbid.mm";

theorem imbi1d(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume imbid.1: |- "( ph -> ( ps <-> ch ) )";





  do {
    wph;
    wps;
    wth;
    wi;
    wch;
    wth;
    wi;
    wph;
    wch;
    wps;
    wth;
    wph;
    wps;
    wch;
    imbid.1;
    biimprd;
    imim1d;
    wph;
    wps;
    wch;
    wth;
    wph;
    wps;
    wch;
    imbid.1;
    biimpd;
    imim1d;
    impbid;
  };

  return '|-' "( ph -> ( ( ps -> th ) <-> ( ch -> th ) ) )";
}
