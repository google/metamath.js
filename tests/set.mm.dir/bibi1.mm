include "wb.mm";
include "id.mm";
include "bibi1d.mm";

theorem bibi1(wph: wff ph, wps: wff ps, wch: wff ch) {





  do {
    wph;
    wps;
    wb;
    #;
    wph;
    wps;
    wch;
    @0;
    id;
    bibi1d;
  };

  return |- "( ( ph <-> ps ) -> ( ( ph <-> ch ) <-> ( ps <-> ch ) ) )";
}
