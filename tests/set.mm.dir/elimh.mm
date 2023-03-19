include "wif.mm"
include "wb.mm"
include "ifptru.mm"
include "syl.mm"
include "ibi.mm"
include "wn.mm"
include "ifpfal.mm"
include "mpbii.mm"
include "pm2.61i.mm"

theorem elimh
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume elimh.1: |- ( ( if- ( ch , ph , ps ) <-> ph ) -> ( ch <-> ta ) )
  assume elimh.2: |- ( ( if- ( ch , ph , ps ) <-> ps ) -> ( th <-> ta ) )
  assume elimh.3: |- th


  assert |- ta

  proof
    wch
    wta
    wch
    wta
    wch
    wch
    wph
    wps
    wif
    #
    wph
    wb
    wch
    wta
    wb
    wch
    wph
    wps
    ifptru
    elimh.1
    syl
    ibi
    wch
    wn
    #
    wth
    wta
    elimh.3
    @1
    @0
    wps
    wb
    wth
    wta
    wb
    wch
    wph
    wps
    ifpfal
    elimh.2
    syl
    mpbii
    pm2.61i
end
