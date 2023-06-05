include "wb.mm";
include "wi.mm";
include "pm5.74i.mm";
include "bibi2i.mm";
include "pm5.74.mm";
include "3bitr4i.mm";
include "pm5.74ri.mm";

theorem bibi2d(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume imbid.1: |- "( ph -> ( ps <-> ch ) )";





  do {
    wph;
    wth;
    wps;
    wb;
    #;
    wth;
    wch;
    wb;
    #;
    wph;
    wth;
    wi;
    #;
    wph;
    wps;
    wi;
    #;
    wb;
    @2;
    wph;
    wch;
    wi;
    #;
    wb;
    wph;
    @0;
    wi;
    wph;
    @1;
    wi;
    @3;
    @4;
    @2;
    wph;
    wps;
    wch;
    imbid.1;
    pm5.74i;
    bibi2i;
    wph;
    wth;
    wps;
    pm5.74;
    wph;
    wth;
    wch;
    pm5.74;
    3bitr4i;
    pm5.74ri;
  };

  return |- "( ph -> ( ( th <-> ps ) <-> ( th <-> ch ) ) )";
}
