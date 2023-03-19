include "c0.mm"
include "wceq.mm"
include "ccda.mm"
include "co.mm"
include "csdm.mm"
include "wbr.mm"
include "wo.mm"
include "c2o.mm"
include "cxp.mm"
include "cfin5.mm"
include "wcel.mm"
include "cfin6.mm"
include "c1o.mm"
include "cen.mm"
include "orc.mm"
include "sdom2en01.mm"
include "sylibr.mm"
include "orcd.mm"
include "wn.mm"
include "cdom.mm"
include "cfn.mm"
include "cvv.mm"
include "wb.mm"
include "com.mm"
include "con0.mm"
include "cin.mm"
include "onfin2.mm"
include "inss2.mm"
include "eqsstri.mm"
include "2onn.mm"
include "sselii.mm"
include "relsdom.mm"
include "brrelexi.mm"
include "fidomtri.mm"
include "sylancr.mm"
include "wa.mm"
include "xp2cda.mm"
include "syl.mm"
include "adantr.mm"
include "xpdom2g.mm"
include "sylan.mm"
include "eqbrtrrd.mm"
include "sdomdomtr.mm"
include "syldan.mm"
include "ex.mm"
include "sylbird.mm"
include "orrd.mm"
include "jaoi.mm"
include "isfin5.mm"
include "isfin6.mm"
include "3imtr4i.mm"

theorem fin56
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cV: class V


  assert |- ( A e. Fin5 -> A e. Fin6 )

  proof
    cA
    c0
    wceq
    #
    cA
    cA
    cA
    ccda
    co
    #
    csdm
    wbr
    #
    wo
    cA
    c2o
    csdm
    wbr
    #
    cA
    cA
    cA
    cxp
    #
    csdm
    wbr
    #
    wo
    #
    cA
    cfin5
    wcel
    cA
    cfin6
    wcel
    @0
    @6
    @2
    @0
    @3
    @5
    @0
    @0
    cA
    c1o
    cen
    wbr
    #
    wo
    @3
    @0
    @7
    orc
    cA
    sdom2en01
    sylibr
    orcd
    @2
    @3
    @5
    @2
    @3
    wn
    #
    c2o
    cA
    cdom
    wbr
    #
    @5
    @2
    c2o
    cfn
    wcel
    cA
    cvv
    wcel
    #
    @9
    @8
    wb
    com
    cfn
    c2o
    com
    con0
    cfn
    cin
    cfn
    onfin2
    con0
    cfn
    inss2
    eqsstri
    2onn
    sselii
    cA
    @1
    csdm
    relsdom
    brrelexi
    #
    c2o
    cA
    cvv
    fidomtri
    sylancr
    @2
    @9
    @5
    @2
    @9
    @1
    @4
    cdom
    wbr
    @5
    @2
    @9
    wa
    cA
    c2o
    cxp
    #
    @1
    @4
    cdom
    @2
    @12
    @1
    wceq
    #
    @9
    @2
    @10
    @13
    @11
    cA
    cvv
    xp2cda
    syl
    adantr
    @2
    @10
    @9
    @12
    @4
    cdom
    wbr
    @11
    c2o
    cA
    cA
    cvv
    xpdom2g
    sylan
    eqbrtrrd
    cA
    @1
    @4
    sdomdomtr
    syldan
    ex
    sylbird
    orrd
    jaoi
    cA
    isfin5
    cA
    isfin6
    3imtr4i
end
