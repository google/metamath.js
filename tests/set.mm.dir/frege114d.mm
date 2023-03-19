include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "w3o.mm"
include "df-3or.mm"
include "biimpri.mm"
include "orcs.mm"
include "syl.mm"

theorem frege114d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  assume frege114d.ab: |- ( ph -> ( A R B \/ A = B ) )


  assert |- ( ph -> ( A R B \/ A = B \/ B R A ) )

  proof
    wph
    cA
    cB
    cR
    wbr
    #
    cA
    cB
    wceq
    #
    wo
    #
    @0
    @1
    cB
    cA
    cR
    wbr
    #
    w3o
    #
    frege114d.ab
    @2
    @3
    @4
    @4
    @2
    @3
    wo
    @0
    @1
    @3
    df-3or
    biimpri
    orcs
    syl
end
