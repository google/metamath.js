include "wn.mm";
include "wi.mm";
include "wo.mm";
include "imbi2d.mm";
include "df-or.mm";
include "3bitr4g.mm";

theorem orbi2d(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume bid.1: |- "( ph -> ( ps <-> ch ) )";





  do {
    wph;
    wth;
    wn;
    #;
    wps;
    wi;
    @0;
    wch;
    wi;
    wth;
    wps;
    wo;
    wth;
    wch;
    wo;
    wph;
    wps;
    wch;
    @0;
    bid.1;
    imbi2d;
    wth;
    wps;
    df-or;
    wth;
    wch;
    df-or;
    3bitr4g;
  };

  return '|-' "( ph -> ( ( th \\/ ps ) <-> ( th \\/ ch ) ) )";
}
