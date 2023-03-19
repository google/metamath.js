include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "ccj.mm"
include "cfv.mm"
include "cmin.mm"
include "cjreim.mm"
include "fveq2d.mm"
include "cc.mm"
include "wceq.mm"
include "simpl.mm"
include "recnd.mm"
include "ax-icn.mm"
include "a1i.mm"
include "simpr.mm"
include "mulcld.mm"
include "addcld.mm"
include "cjcj.mm"
include "syl.mm"
include "eqtr3d.mm"

theorem cjreim2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( * ` ( A - ( _i x. B ) ) ) = ( A + ( _i x. B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    ci
    cB
    cmul
    co
    #
    caddc
    co
    #
    ccj
    cfv
    #
    ccj
    cfv
    #
    cA
    @3
    cmin
    co
    #
    ccj
    cfv
    @4
    @2
    @5
    @7
    ccj
    cA
    cB
    cjreim
    fveq2d
    @2
    @4
    cc
    wcel
    @6
    @4
    wceq
    @2
    cA
    @3
    @2
    cA
    @0
    @1
    simpl
    recnd
    @2
    ci
    cB
    ci
    cc
    wcel
    @2
    ax-icn
    a1i
    @2
    cB
    @0
    @1
    simpr
    recnd
    mulcld
    addcld
    @4
    cjcj
    syl
    eqtr3d
end
