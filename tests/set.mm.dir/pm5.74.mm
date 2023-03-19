include "wb.mm"
include "wi.mm"
include "biimp.mm"
include "imim3i.mm"
include "biimpr.mm"
include "impbid.mm"
include "pm2.86d.mm"
include "impbidd.mm"
include "impbii.mm"

theorem pm5.74
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps <-> ch ) ) <-> ( ( ph -> ps ) <-> ( ph -> ch ) ) )

  proof
    wph
    wps
    wch
    wb
    #
    wi
    #
    wph
    wps
    wi
    #
    wph
    wch
    wi
    #
    wb
    #
    @1
    @2
    @3
    @0
    wps
    wch
    wph
    wps
    wch
    biimp
    imim3i
    @0
    wch
    wps
    wph
    wps
    wch
    biimpr
    imim3i
    impbid
    @4
    wph
    wps
    wch
    @4
    wph
    wps
    wch
    @2
    @3
    biimp
    pm2.86d
    @4
    wph
    wch
    wps
    @2
    @3
    biimpr
    pm2.86d
    impbidd
    impbii
end
