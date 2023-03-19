include "wcel.mm"
include "w3a.mm"
include "ccda.mm"
include "co.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "c1o.mm"
include "cun.mm"
include "cen.mm"
include "wbr.mm"
include "cin.mm"
include "wceq.mm"
include "cvv.mm"
include "simp1.mm"
include "0ex.mm"
include "xpsneng.mm"
include "sylancl.mm"
include "ensymd.mm"
include "con0.mm"
include "simp2.mm"
include "snex.mm"
include "xpexg.mm"
include "1on.mm"
include "entr.mm"
include "syl2anc.mm"
include "xp01disj.mm"
include "a1i.mm"
include "cdaenun.mm"
include "syl3anc.mm"
include "simp3.mm"
include "indir.mm"
include "xpeq1i.mm"
include "xpindir.mm"
include "0xp.mm"
include "3eqtr3i.mm"
include "uneq12i.mm"
include "un0.mm"
include "3eqtri.mm"
include "wa.mm"
include "ovex.mm"
include "cdaval.mm"
include "mpan2.mm"
include "xpeq1d.mm"
include "xpundir.mm"
include "syl6eq.mm"
include "uneq2d.mm"
include "unass.mm"
include "syl6eqr.mm"
include "sylan9eq.mm"
include "3impb.mm"
include "breqtrrd.mm"

theorem cdaassen
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( ( A +c B ) +c C ) ~~ ( A +c ( B +c C ) ) )

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
    ccda
    co
    #
    cC
    ccda
    co
    #
    cA
    c0
    csn
    #
    cxp
    #
    cB
    @6
    cxp
    #
    c1o
    csn
    #
    cxp
    #
    cun
    #
    cC
    @9
    cxp
    #
    @9
    cxp
    #
    cun
    #
    cA
    cB
    cC
    ccda
    co
    #
    ccda
    co
    #
    cen
    @3
    @4
    @11
    cen
    wbr
    #
    cC
    @13
    cen
    wbr
    @11
    @13
    cin
    #
    c0
    wceq
    #
    @5
    @14
    cen
    wbr
    @3
    cA
    @7
    cen
    wbr
    cB
    @10
    cen
    wbr
    @7
    @10
    cin
    c0
    wceq
    #
    @17
    @3
    @7
    cA
    @3
    @0
    c0
    cvv
    wcel
    #
    @7
    cA
    cen
    wbr
    @0
    @1
    @2
    simp1
    0ex
    cA
    c0
    cV
    cvv
    xpsneng
    sylancl
    ensymd
    @3
    @10
    cB
    @3
    @10
    @8
    cen
    wbr
    #
    @8
    cB
    cen
    wbr
    #
    @10
    cB
    cen
    wbr
    @3
    @8
    cvv
    wcel
    #
    c1o
    con0
    wcel
    #
    @22
    @3
    @1
    @6
    cvv
    wcel
    @24
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
    1on
    @8
    c1o
    cvv
    con0
    xpsneng
    sylancl
    @3
    @1
    @21
    @23
    @26
    0ex
    cB
    c0
    cW
    cvv
    xpsneng
    sylancl
    @10
    @8
    cB
    entr
    syl2anc
    ensymd
    @20
    @3
    cA
    @8
    xp01disj
    a1i
    cA
    @7
    cB
    @10
    cdaenun
    syl3anc
    @3
    @13
    cC
    @3
    @13
    @12
    cen
    wbr
    #
    @12
    cC
    cen
    wbr
    #
    @13
    cC
    cen
    wbr
    @3
    @12
    cvv
    wcel
    #
    @25
    @27
    @3
    @2
    @9
    cvv
    wcel
    @29
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
    1on
    @12
    c1o
    cvv
    con0
    xpsneng
    sylancl
    @3
    @2
    @25
    @28
    @30
    1on
    cC
    c1o
    cX
    con0
    xpsneng
    sylancl
    @13
    @12
    cC
    entr
    syl2anc
    ensymd
    @19
    @3
    @18
    @7
    @13
    cin
    #
    @10
    @13
    cin
    #
    cun
    c0
    c0
    cun
    c0
    @7
    @10
    @13
    indir
    @31
    c0
    @32
    c0
    cA
    @12
    xp01disj
    @8
    @12
    cin
    #
    @9
    cxp
    c0
    @9
    cxp
    @32
    c0
    @33
    c0
    @9
    cB
    cC
    xp01disj
    xpeq1i
    @8
    @12
    @9
    xpindir
    @9
    0xp
    3eqtr3i
    uneq12i
    c0
    un0
    3eqtri
    a1i
    @4
    @11
    cC
    @13
    cdaenun
    syl3anc
    @0
    @1
    @2
    @16
    @14
    wceq
    @0
    @1
    @2
    wa
    #
    @16
    @7
    @15
    @9
    cxp
    #
    cun
    #
    @14
    @0
    @15
    cvv
    wcel
    @16
    @36
    wceq
    cB
    cC
    ccda
    ovex
    cA
    @15
    cV
    cvv
    cdaval
    mpan2
    @34
    @36
    @7
    @10
    @13
    cun
    #
    cun
    @14
    @34
    @35
    @37
    @7
    @34
    @35
    @8
    @12
    cun
    #
    @9
    cxp
    @37
    @34
    @15
    @38
    @9
    cB
    cC
    cW
    cX
    cdaval
    xpeq1d
    @8
    @12
    @9
    xpundir
    syl6eq
    uneq2d
    @7
    @10
    @13
    unass
    syl6eqr
    sylan9eq
    3impb
    breqtrrd
end
