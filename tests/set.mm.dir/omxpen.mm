include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "comu.mm"
include "co.mm"
include "cen.mm"
include "wbr.mm"
include "xpcomeng.mm"
include "cvv.mm"
include "cv.mm"
include "coa.mm"
include "cmpt2.mm"
include "wf1o.mm"
include "xpexg.mm"
include "ancoms.mm"
include "omcl.mm"
include "eqid.mm"
include "omxpenlem.mm"
include "f1oen2g.mm"
include "syl3anc.mm"
include "entr.mm"
include "syl2anc.mm"
include "ensymd.mm"

theorem omxpen
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. On /\ B e. On ) -> ( A .o B ) ~~ ( A X. B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cA
    cB
    cxp
    #
    cA
    cB
    comu
    co
    #
    @2
    @3
    cB
    cA
    cxp
    #
    cen
    wbr
    @5
    @4
    cen
    wbr
    #
    @3
    @4
    cen
    wbr
    cA
    cB
    con0
    con0
    xpcomeng
    @2
    @5
    cvv
    wcel
    #
    @4
    con0
    wcel
    @5
    @4
    vx
    vy
    cB
    cA
    cA
    vx
    cv
    comu
    co
    vy
    cv
    coa
    co
    cmpt2
    #
    wf1o
    @6
    @1
    @0
    @7
    cB
    cA
    con0
    con0
    xpexg
    ancoms
    cA
    cB
    omcl
    vx
    vy
    cA
    cB
    @8
    @8
    eqid
    omxpenlem
    @5
    @4
    @8
    cvv
    con0
    f1oen2g
    syl3anc
    @3
    @5
    @4
    entr
    syl2anc
    ensymd
end
