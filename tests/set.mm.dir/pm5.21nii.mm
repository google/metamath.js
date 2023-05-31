include "wb.mm";
include "pm5.21ni.mm";
include "pm2.61i.mm";

theorem pm5.21nii(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume pm5.21ni.1: $|- ( ph -> ps )$;
  assume pm5.21ni.2: $|- ( ch -> ps )$;
  assume pm5.21nii.3: $|- ( ps -> ( ph <-> ch ) )$;





  do {
    wps;
    wph;
    wch;
    wb;
    pm5.21nii.3;
    wph;
    wps;
    wch;
    pm5.21ni.1;
    pm5.21ni.2;
    pm5.21ni;
    pm2.61i;
  };

  return $|-$ $( ph <-> ch )$;
}
