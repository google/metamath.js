include "wif.mm"
include "wi.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "dfifp3.mm"
include "imor.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem dfifp4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( if- ( ph , ps , ch ) <-> ( ( -. ph \/ ps ) /\ ( ph \/ ch ) ) )

  proof
    wph
    wps
    wch
    wif
    wph
    wps
    wi
    #
    wph
    wch
    wo
    #
    wa
    wph
    wn
    wps
    wo
    #
    @1
    wa
    wph
    wps
    wch
    dfifp3
    @0
    @2
    @1
    wph
    wps
    imor
    anbi1i
    bitri
end
