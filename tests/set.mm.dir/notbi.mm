include "wb.mm";
include "wn.mm";
include "id.mm";
include "notbid.mm";
include "con4bid.mm";
include "impbii.mm";

theorem notbi(wph: wff ph, wps: wff ps) {





  do {
    wph;
    wps;
    wb;
    #;
    wph;
    wn;
    wps;
    wn;
    wb;
    #;
    @0;
    wph;
    wps;
    @0;
    id;
    notbid;
    @1;
    wph;
    wps;
    @1;
    id;
    con4bid;
    impbii;
  };

  return |- "( ( ph <-> ps ) <-> ( -. ph <-> -. ps ) )";
}
