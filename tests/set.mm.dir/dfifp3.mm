include "wif.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "dfifp2.mm"
include "pm4.64.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem dfifp3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( if- ( ph , ps , ch ) <-> ( ( ph -> ps ) /\ ( ph \/ ch ) ) )

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
    wch
    wi
    #
    wa
    @0
    wph
    wch
    wo
    #
    wa
    wph
    wps
    wch
    dfifp2
    @1
    @2
    @0
    wph
    wch
    pm4.64
    anbi2i
    bitri
end
