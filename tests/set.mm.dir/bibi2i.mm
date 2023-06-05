include "wb.mm";
include "id.mm";
include "syl6bb.mm";
include "syl6bbr.mm";
include "impbii.mm";

theorem bibi2i(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume bibi2i.1: |- "( ph <-> ps )";





  do {
    wch;
    wph;
    wb;
    #;
    wch;
    wps;
    wb;
    #;
    @0;
    wch;
    wph;
    wps;
    @0;
    id;
    bibi2i.1;
    syl6bb;
    @1;
    wch;
    wps;
    wph;
    @1;
    id;
    bibi2i.1;
    syl6bbr;
    impbii;
  };

  return |- "( ( ch <-> ph ) <-> ( ch <-> ps ) )";
}
