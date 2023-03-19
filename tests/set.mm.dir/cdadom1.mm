include "cdom.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "ccda.mm"
include "co.mm"
include "wa.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "c1o.mm"
include "cun.mm"
include "snex.mm"
include "xpdom1.mm"
include "xpexg.mm"
include "mpan2.mm"
include "domrefg.mm"
include "syl.mm"
include "cin.mm"
include "wceq.mm"
include "xp01disj.mm"
include "undom.mm"
include "syl2an.mm"
include "reldom.mm"
include "brrelexi.mm"
include "cdaval.mm"
include "sylan.mm"
include "brrelex2i.mm"
include "3brtr4d.mm"
include "wn.mm"
include "simpr.mm"
include "intnand.mm"
include "wfn.mm"
include "cdm.mm"
include "cdafn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "ovex.mm"
include "0dom.mm"
include "syl6eqbr.mm"
include "pm2.61dan.mm"

theorem cdadom1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A ~<_ B -> ( A +c C ) ~<_ ( B +c C ) )

  proof
    cA
    cB
    cdom
    wbr
    #
    cC
    cvv
    wcel
    #
    cA
    cC
    ccda
    co
    #
    cB
    cC
    ccda
    co
    #
    cdom
    wbr
    @0
    @1
    wa
    cA
    c0
    csn
    #
    cxp
    #
    cC
    c1o
    csn
    #
    cxp
    #
    cun
    #
    cB
    @4
    cxp
    #
    @7
    cun
    #
    @2
    @3
    cdom
    @0
    @5
    @9
    cdom
    wbr
    #
    @7
    @7
    cdom
    wbr
    #
    @8
    @10
    cdom
    wbr
    #
    @1
    cA
    cB
    @4
    c0
    snex
    xpdom1
    @1
    @7
    cvv
    wcel
    #
    @12
    @1
    @6
    cvv
    wcel
    @14
    c1o
    snex
    cC
    @6
    cvv
    cvv
    xpexg
    mpan2
    @7
    cvv
    domrefg
    syl
    @11
    @12
    wa
    @9
    @7
    cin
    c0
    wceq
    @13
    cB
    cC
    xp01disj
    @5
    @9
    @7
    @7
    undom
    mpan2
    syl2an
    @0
    cA
    cvv
    wcel
    #
    @1
    @2
    @8
    wceq
    cA
    cB
    cdom
    reldom
    brrelexi
    cA
    cC
    cvv
    cvv
    cdaval
    sylan
    @0
    cB
    cvv
    wcel
    @1
    @3
    @10
    wceq
    cA
    cB
    cdom
    reldom
    brrelex2i
    cB
    cC
    cvv
    cvv
    cdaval
    sylan
    3brtr4d
    @0
    @1
    wn
    #
    wa
    #
    @2
    c0
    @3
    cdom
    @17
    @15
    @1
    wa
    wn
    @2
    c0
    wceq
    @17
    @1
    @15
    @0
    @16
    simpr
    intnand
    cA
    cC
    cvv
    ccda
    ccda
    cvv
    cvv
    cxp
    #
    wfn
    ccda
    cdm
    @18
    wceq
    cdafn
    @18
    ccda
    fndm
    ax-mp
    ndmov
    syl
    @3
    cB
    cC
    ccda
    ovex
    0dom
    syl6eqbr
    pm2.61dan
end
