include "wss.mm"
include "wfr.mm"
include "wor.mm"
include "wa.mm"
include "wwe.mm"
include "frss.mm"
include "soss.mm"
include "anim12d.mm"
include "df-we.mm"
include "3imtr4g.mm"

theorem wess
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( A C_ B -> ( R We B -> R We A ) )

  proof
    cA
    cB
    wss
    #
    cB
    cR
    wfr
    #
    cB
    cR
    wor
    #
    wa
    cA
    cR
    wfr
    #
    cA
    cR
    wor
    #
    wa
    cB
    cR
    wwe
    cA
    cR
    wwe
    @0
    @1
    @3
    @2
    @4
    cA
    cB
    cR
    frss
    cA
    cB
    cR
    soss
    anim12d
    cB
    cR
    df-we
    cA
    cR
    df-we
    3imtr4g
end
