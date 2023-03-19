include "wi.mm"
include "wif.mm"
include "biimt.mm"
include "wo.mm"
include "wa.mm"
include "orc.mm"
include "biantrud.mm"
include "dfifp3.mm"
include "syl6bbr.mm"
include "bitr2d.mm"

theorem ifptru
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ph -> ( if- ( ph , ps , ch ) <-> ps ) )

  proof
    wph
    wps
    wph
    wps
    wi
    #
    wph
    wps
    wch
    wif
    #
    wph
    wps
    biimt
    wph
    @0
    @0
    wph
    wch
    wo
    #
    wa
    @1
    wph
    @2
    @0
    wph
    wch
    orc
    biantrud
    wph
    wps
    wch
    dfifp3
    syl6bbr
    bitr2d
end
