include "wa.mm"
include "wi.mm"
include "iba.mm"
include "wb.mm"
include "ax-1.mm"
include "biimt.mm"
include "syl.mm"
include "bitrd.mm"

theorem dedlem0a
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch


  assert |- ( ph -> ( ps <-> ( ( ch -> ph ) -> ( ps /\ ph ) ) ) )

  proof
    wph
    wps
    wps
    wph
    wa
    #
    wch
    wph
    wi
    #
    @0
    wi
    #
    wph
    wps
    iba
    wph
    @1
    @0
    @2
    wb
    wph
    wch
    ax-1
    @1
    @0
    biimt
    syl
    bitrd
end
