include "wcel.mm"
include "w3a.mm"
include "cxp.mm"
include "ccda.mm"
include "co.mm"
include "c0.mm"
include "csn.mm"
include "c1o.mm"
include "cun.mm"
include "cen.mm"
include "wbr.mm"
include "cin.mm"
include "wceq.mm"
include "enrefg.mm"
include "3ad2ant1.mm"
include "cvv.mm"
include "simp2.mm"
include "0ex.mm"
include "xpsneng.mm"
include "sylancl.mm"
include "ensymd.mm"
include "xpen.mm"
include "syl2anc.mm"
include "con0.mm"
include "simp3.mm"
include "1on.mm"
include "xp01disj.mm"
include "xpeq2i.mm"
include "xpindi.mm"
include "xp0.mm"
include "3eqtr3i.mm"
include "a1i.mm"
include "cdaenun.mm"
include "syl3anc.mm"
include "cdaval.mm"
include "3adant1.mm"
include "xpeq2d.mm"
include "xpundi.mm"
include "syl6eq.mm"
include "breqtrrd.mm"

theorem xpcdaen
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( A X. ( B +c C ) ) ~~ ( ( A X. B ) +c ( A X. C ) ) )

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
    cxp
    #
    cA
    cC
    cxp
    #
    ccda
    co
    #
    cA
    cB
    cC
    ccda
    co
    #
    cxp
    #
    @3
    @6
    cA
    cB
    c0
    csn
    cxp
    #
    cxp
    #
    cA
    cC
    c1o
    csn
    cxp
    #
    cxp
    #
    cun
    #
    @8
    cen
    @3
    @4
    @10
    cen
    wbr
    #
    @5
    @12
    cen
    wbr
    #
    @10
    @12
    cin
    #
    c0
    wceq
    #
    @6
    @13
    cen
    wbr
    @3
    cA
    cA
    cen
    wbr
    #
    cB
    @9
    cen
    wbr
    @14
    @0
    @1
    @18
    @2
    cA
    cV
    enrefg
    3ad2ant1
    #
    @3
    @9
    cB
    @3
    @1
    c0
    cvv
    wcel
    @9
    cB
    cen
    wbr
    @0
    @1
    @2
    simp2
    0ex
    cB
    c0
    cW
    cvv
    xpsneng
    sylancl
    ensymd
    cA
    cA
    cB
    @9
    xpen
    syl2anc
    @3
    @18
    cC
    @11
    cen
    wbr
    @15
    @19
    @3
    @11
    cC
    @3
    @2
    c1o
    con0
    wcel
    @11
    cC
    cen
    wbr
    @0
    @1
    @2
    simp3
    1on
    cC
    c1o
    cX
    con0
    xpsneng
    sylancl
    ensymd
    cA
    cA
    cC
    @11
    xpen
    syl2anc
    @17
    @3
    cA
    @9
    @11
    cin
    #
    cxp
    cA
    c0
    cxp
    @16
    c0
    @20
    c0
    cA
    cB
    cC
    xp01disj
    xpeq2i
    cA
    @9
    @11
    xpindi
    cA
    xp0
    3eqtr3i
    a1i
    @4
    @10
    @5
    @12
    cdaenun
    syl3anc
    @3
    @8
    cA
    @9
    @11
    cun
    #
    cxp
    @13
    @3
    @7
    @21
    cA
    @1
    @2
    @7
    @21
    wceq
    @0
    cB
    cC
    cW
    cX
    cdaval
    3adant1
    xpeq2d
    cA
    @9
    @11
    xpundi
    syl6eq
    breqtrrd
    ensymd
end
