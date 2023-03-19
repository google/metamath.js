include "wif.mm"
include "wa.mm"
include "wo.mm"
include "anifp.mm"
include "bj-jaoi2.mm"
include "orc.mm"
include "impbii.mm"

theorem bj-consensus
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( if- ( ph , ps , ch ) \/ ( ps /\ ch ) ) <-> if- ( ph , ps , ch ) )

  proof
    wph
    wps
    wch
    wif
    #
    wps
    wch
    wa
    #
    wo
    @0
    @1
    @0
    wph
    wps
    wch
    anifp
    bj-jaoi2
    @0
    @1
    orc
    impbii
end
