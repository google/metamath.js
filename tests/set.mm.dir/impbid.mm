include "wb.mm"
include "impbid21d.mm"
include "pm2.43i.mm"

theorem impbid
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume impbid.1: |- ( ph -> ( ps -> ch ) )
  assume impbid.2: |- ( ph -> ( ch -> ps ) )


  assert |- ( ph -> ( ps <-> ch ) )

  proof
    wph
    wps
    wch
    wb
    wph
    wph
    wps
    wch
    impbid.1
    impbid.2
    impbid21d
    pm2.43i
end
