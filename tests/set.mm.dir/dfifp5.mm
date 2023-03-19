include "wif.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "dfifp2.mm"
include "imor.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem dfifp5
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( if- ( ph , ps , ch ) <-> ( ( -. ph \/ ps ) /\ ( -. ph -> ch ) ) )

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
    wn
    #
    wch
    wi
    #
    wa
    @1
    wps
    wo
    #
    @2
    wa
    wph
    wps
    wch
    dfifp2
    @0
    @3
    @2
    wph
    wps
    imor
    anbi1i
    bitri
end
