include "wif.mm"
include "wb.mm"
include "ifptru.mm"
include "mpbiri.mm"
include "syl.mm"

theorem dedt
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume dedt.1: |- ( ( if- ( ch , ph , ps ) <-> ph ) -> ( th <-> ta ) )
  assume dedt.2: |- ta


  assert |- ( ch -> th )

  proof
    wch
    wch
    wph
    wps
    wif
    wph
    wb
    #
    wth
    wch
    wph
    wps
    ifptru
    @0
    wth
    wta
    dedt.2
    dedt.1
    mpbiri
    syl
end
