include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "ccxp.mm"
include "wb.mm"
include "simprl.mm"
include "crp.mm"
include "rplogcl.mm"
include "adantr.mm"
include "rpred.mm"
include "remulcld.mm"
include "simprr.mm"
include "eflt.mm"
include "syl2anc.mm"
include "ltmul1d.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "simpll.mm"
include "recnd.mm"
include "0red.mm"
include "1red.mm"
include "0lt1.mm"
include "a1i.mm"
include "simplr.mm"
include "lttrd.mm"
include "gt0ne0d.mm"
include "cxpef.mm"
include "syl3anc.mm"
include "breq12d.mm"
include "3bitr4d.mm"

theorem cxplt
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR /\ 1 < A ) /\ ( B e. RR /\ C e. RR ) ) -> ( B < C <-> ( A ^c B ) < ( A ^c C ) ) )

  proof
    cA
    cr
    wcel
    #
    c1
    cA
    clt
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    wa
    #
    wa
    #
    cB
    cA
    clog
    cfv
    #
    cmul
    co
    #
    cC
    @7
    cmul
    co
    #
    clt
    wbr
    #
    @8
    ce
    cfv
    #
    @9
    ce
    cfv
    #
    clt
    wbr
    #
    cB
    cC
    clt
    wbr
    cA
    cB
    ccxp
    co
    #
    cA
    cC
    ccxp
    co
    #
    clt
    wbr
    @6
    @8
    cr
    wcel
    @9
    cr
    wcel
    @10
    @13
    wb
    @6
    cB
    @7
    @2
    @3
    @4
    simprl
    #
    @6
    @7
    @2
    @7
    crp
    wcel
    @5
    cA
    rplogcl
    adantr
    #
    rpred
    #
    remulcld
    @6
    cC
    @7
    @2
    @3
    @4
    simprr
    #
    @18
    remulcld
    @8
    @9
    eflt
    syl2anc
    @6
    cB
    cC
    @7
    @16
    @19
    @17
    ltmul1d
    @6
    @14
    @11
    @15
    @12
    clt
    @6
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cB
    cc
    wcel
    @14
    @11
    wceq
    @6
    cA
    @0
    @1
    @5
    simpll
    #
    recnd
    #
    @6
    cA
    @6
    cc0
    c1
    cA
    @6
    0red
    @6
    1red
    @22
    cc0
    c1
    clt
    wbr
    @6
    0lt1
    a1i
    @0
    @1
    @5
    simplr
    lttrd
    gt0ne0d
    #
    @6
    cB
    @16
    recnd
    cA
    cB
    cxpef
    syl3anc
    @6
    @20
    @21
    cC
    cc
    wcel
    @15
    @12
    wceq
    @23
    @24
    @6
    cC
    @19
    recnd
    cA
    cC
    cxpef
    syl3anc
    breq12d
    3bitr4d
end
