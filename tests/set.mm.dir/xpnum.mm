include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "wrex.mm"
include "cxp.mm"
include "isnum2.mm"
include "wa.mm"
include "reeanv.mm"
include "comu.mm"
include "co.mm"
include "omcl.mm"
include "adantr.mm"
include "omxpen.mm"
include "xpen.mm"
include "entr.mm"
include "syl2an.mm"
include "isnumi.mm"
include "syl2anc.mm"
include "ex.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"

theorem xpnum
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. dom card /\ B e. dom card ) -> ( A X. B ) e. dom card )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    vx
    cv
    #
    cA
    cen
    wbr
    #
    vx
    con0
    wrex
    #
    vy
    cv
    #
    cB
    cen
    wbr
    #
    vy
    con0
    wrex
    #
    cA
    cB
    cxp
    #
    @0
    wcel
    #
    cB
    @0
    wcel
    vx
    cA
    isnum2
    vy
    cB
    isnum2
    @3
    @6
    wa
    @2
    @5
    wa
    #
    vy
    con0
    wrex
    vx
    con0
    wrex
    @8
    @2
    @5
    vx
    vy
    con0
    con0
    reeanv
    @9
    @8
    vx
    vy
    con0
    con0
    @1
    con0
    wcel
    @4
    con0
    wcel
    wa
    #
    @9
    @8
    @10
    @9
    wa
    @1
    @4
    comu
    co
    #
    con0
    wcel
    #
    @11
    @7
    cen
    wbr
    #
    @8
    @10
    @12
    @9
    @1
    @4
    omcl
    adantr
    @10
    @11
    @1
    @4
    cxp
    #
    cen
    wbr
    @14
    @7
    cen
    wbr
    @13
    @9
    @1
    @4
    omxpen
    @1
    cA
    @4
    cB
    xpen
    @11
    @14
    @7
    entr
    syl2an
    @11
    @7
    isnumi
    syl2anc
    ex
    rexlimivv
    sylbir
    syl2anb
end
