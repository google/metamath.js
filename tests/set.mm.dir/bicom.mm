include "wb.mm";
include "bicom1.mm";
include "impbii.mm";

theorem bicom(wph: 'wff' ph, wps: 'wff' ps) {





  do {
    wph;
    wps;
    wb;
    wps;
    wph;
    wb;
    wph;
    wps;
    bicom1;
    wps;
    wph;
    bicom1;
    impbii;
  };

  return '|-' "( ( ph <-> ps ) <-> ( ps <-> ph ) )";
}
