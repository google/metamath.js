include "wcel.mm"
include "w3a.mm"
include "ccda.mm"
include "co.mm"
include "cmap.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "cun.mm"
include "wceq.mm"
include "cdaval.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "cvv.mm"
include "cin.mm"
include "simp2.mm"
include "snex.mm"
include "xpexg.mm"
include "sylancl.mm"
include "simp3.mm"
include "simp1.mm"
include "xp01disj.mm"
include "a1i.mm"
include "mapunen.mm"
include "syl31anc.mm"
include "eqbrtrd.mm"
include "enrefg.mm"
include "syl.mm"
include "0ex.mm"
include "xpsneng.mm"
include "mapen.mm"
include "syl2anc.mm"
include "con0.mm"
include "1on.mm"
include "xpen.mm"
include "entr.mm"

theorem mapcdaen
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( A ^m ( B +c C ) ) ~~ ( ( A ^m B ) X. ( A ^m C ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cC
    ccda
    co
    #
    cmap
    co
    #
    cA
    cB
    c0
    csn
    #
    cxp
    #
    cmap
    co
    #
    cA
    cC
    c1o
    csn
    #
    cxp
    #
    cmap
    co
    #
    cxp
    #
    cen
    wbr
    @12
    cA
    cB
    cmap
    co
    #
    cA
    cC
    cmap
    co
    #
    cxp
    #
    cen
    wbr
    #
    @5
    @15
    cen
    wbr
    @3
    @5
    cA
    @7
    @10
    cun
    #
    cmap
    co
    #
    @12
    cen
    @3
    @4
    @17
    cA
    cmap
    @1
    @2
    @4
    @17
    wceq
    @0
    cB
    cC
    cW
    cX
    cdaval
    3adant1
    oveq2d
    @3
    @7
    cvv
    wcel
    #
    @10
    cvv
    wcel
    #
    @0
    @7
    @10
    cin
    c0
    wceq
    #
    @18
    @12
    cen
    wbr
    @3
    @1
    @6
    cvv
    wcel
    @19
    @0
    @1
    @2
    simp2
    #
    c0
    snex
    cB
    @6
    cW
    cvv
    xpexg
    sylancl
    @3
    @2
    @9
    cvv
    wcel
    @20
    @0
    @1
    @2
    simp3
    #
    c1o
    snex
    cC
    @9
    cX
    cvv
    xpexg
    sylancl
    @0
    @1
    @2
    simp1
    #
    @21
    @3
    cB
    cC
    xp01disj
    a1i
    @7
    @10
    cA
    cvv
    cvv
    cV
    mapunen
    syl31anc
    eqbrtrd
    @3
    @8
    @13
    cen
    wbr
    #
    @11
    @14
    cen
    wbr
    #
    @16
    @3
    cA
    cA
    cen
    wbr
    #
    @7
    cB
    cen
    wbr
    #
    @25
    @3
    @0
    @27
    @24
    cA
    cV
    enrefg
    syl
    #
    @3
    @1
    c0
    cvv
    wcel
    @28
    @22
    0ex
    cB
    c0
    cW
    cvv
    xpsneng
    sylancl
    cA
    cA
    @7
    cB
    mapen
    syl2anc
    @3
    @27
    @10
    cC
    cen
    wbr
    #
    @26
    @29
    @3
    @2
    c1o
    con0
    wcel
    @30
    @23
    1on
    cC
    c1o
    cX
    con0
    xpsneng
    sylancl
    cA
    cA
    @10
    cC
    mapen
    syl2anc
    @8
    @13
    @11
    @14
    xpen
    syl2anc
    @5
    @12
    @15
    entr
    syl2anc
end
