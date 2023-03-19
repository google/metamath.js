include "wfun.mm"
include "wbr.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wrel.mm"
include "wi.mm"
include "funrel.mm"
include "releldm.mm"
include "ex.mm"
include "syl.mm"
include "pm4.71rd.mm"
include "funbrfvb.mm"
include "pm5.32da.mm"
include "bitr4d.mm"

theorem funbrfv2b
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cY: class Y


  assert |- ( Fun F -> ( A F B <-> ( A e. dom F /\ ( F ` A ) = B ) ) )

  proof
    cF
    wfun
    #
    cA
    cB
    cF
    wbr
    #
    cA
    cF
    cdm
    wcel
    #
    @1
    wa
    @2
    cA
    cF
    cfv
    cB
    wceq
    #
    wa
    @0
    @1
    @2
    @0
    cF
    wrel
    #
    @1
    @2
    wi
    cF
    funrel
    @4
    @1
    @2
    cA
    cB
    cF
    releldm
    ex
    syl
    pm4.71rd
    @0
    @2
    @3
    @1
    cA
    cB
    cF
    funbrfvb
    pm5.32da
    bitr4d
end
