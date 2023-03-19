include "csn.mm"
include "wceq.mm"
include "cpr.mm"
include "ctp.mm"
include "w3o.mm"
include "wcel.mm"
include "cfrgr.mm"
include "cv.mm"
include "cdif.mm"
include "wreu.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wo.mm"
include "df-3or.mm"
include "1to2vfriswmgr.mm"
include "expcom.mm"
include "tppreq3.mm"
include "eqeq2d.mm"
include "olc.mm"
include "anim1i.mm"
include "ancomd.mm"
include "syl.mm"
include "ex.mm"
include "syl6bi.mm"
include "cvv.mm"
include "wne.mm"
include "wn.mm"
include "tpprceq3.mm"
include "tprot.mm"
include "eqeq1i.mm"
include "biimpi.mm"
include "prcom.mm"
include "syl6eq.mm"
include "sylan2.mm"
include "a1d.mm"
include "tpcoma.mm"
include "com23.mm"
include "w3a.mm"
include "simpl.mm"
include "anim12i.mm"
include "ad2antrr.mm"
include "3anass.mm"
include "sylibr.mm"
include "simpr.mm"
include "necomd.mm"
include "df-3an.mm"
include "simplr.mm"
include "3vfriswmgr.mm"
include "syl3anc.mm"
include "exp41.mm"
include "ecase.mm"
include "pm2.61ine.mm"
include "jaoi.mm"
include "sylbi.mm"
include "impcom.mm"

theorem 1to3vfriswmgr
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let vh: setvar h
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let vy: setvar y
  let cY: class Y
  assume 3vfriswmgr.v: |- V = ( Vtx ` G )
  assume 3vfriswmgr.e: |- E = ( Edg ` G )

  disjoint A w
  disjoint B w
  disjoint C w
  disjoint E w
  disjoint G w
  disjoint V w
  disjoint X w
  disjoint A h
  disjoint A v
  disjoint h v
  disjoint h w
  disjoint v w
  disjoint B h
  disjoint B v
  disjoint C h
  disjoint C v
  disjoint E h
  disjoint E v
  disjoint V h
  disjoint V v
  disjoint A y
  disjoint w y
  disjoint B y
  disjoint C y
  disjoint E y
  disjoint G y
  disjoint V y
  disjoint X y
  disjoint Y w
  disjoint Y y
  assert |- ( ( A e. X /\ ( V = { A } \/ V = { A , B } \/ V = { A , B , C } ) ) -> ( G e. FriendGraph -> E. h e. V A. v e. ( V \ { h } ) ( { v , h } e. E /\ E! w e. ( V \ { h } ) { v , w } e. E ) ) )

  proof
    cV
    cA
    csn
    wceq
    #
    cV
    cA
    cB
    cpr
    #
    wceq
    #
    cV
    cA
    cB
    cC
    ctp
    #
    wceq
    #
    w3o
    #
    cA
    cX
    wcel
    #
    cG
    cfrgr
    wcel
    vv
    cv
    #
    vh
    cv
    #
    cpr
    cE
    wcel
    @7
    vw
    cv
    cpr
    cE
    wcel
    vw
    cV
    @8
    csn
    cdif
    #
    wreu
    wa
    vv
    @9
    wral
    vh
    cV
    wrex
    wi
    #
    @5
    @0
    @2
    wo
    #
    @4
    wo
    @6
    @10
    wi
    #
    @0
    @2
    @4
    df-3or
    @11
    @12
    @4
    @6
    @11
    @10
    vw
    vv
    cA
    cB
    vh
    cE
    cG
    cV
    cX
    3vfriswmgr.v
    3vfriswmgr.e
    1to2vfriswmgr
    #
    expcom
    @4
    @12
    wi
    #
    cB
    cC
    cB
    cC
    wceq
    #
    @4
    @2
    @12
    @15
    @3
    @1
    cV
    cA
    cB
    cC
    tppreq3
    eqeq2d
    @2
    @6
    @10
    @2
    @6
    wa
    #
    @6
    @11
    wa
    @10
    @16
    @11
    @6
    @2
    @11
    @6
    @2
    @0
    olc
    #
    anim1i
    ancomd
    @13
    syl
    ex
    syl6bi
    cB
    cvv
    wcel
    #
    cB
    cA
    wne
    #
    wa
    #
    cC
    cvv
    wcel
    #
    cC
    cA
    wne
    #
    wa
    #
    cB
    cC
    wne
    #
    @14
    wi
    @20
    wn
    #
    @14
    @24
    @25
    cC
    cA
    cB
    ctp
    #
    cC
    cA
    cpr
    #
    wceq
    #
    @14
    cC
    cA
    cB
    tpprceq3
    @28
    @4
    cV
    cA
    cC
    cpr
    #
    wceq
    #
    @12
    @28
    @3
    @29
    cV
    @28
    @3
    @27
    @29
    @28
    @3
    @27
    wceq
    @26
    @3
    @27
    cC
    cA
    cB
    tprot
    eqeq1i
    biimpi
    cC
    cA
    prcom
    syl6eq
    eqeq2d
    @6
    @30
    @10
    @30
    @6
    @0
    @30
    wo
    @10
    @30
    @0
    olc
    vw
    vv
    cA
    cC
    vh
    cE
    cG
    cV
    cX
    3vfriswmgr.v
    3vfriswmgr.e
    1to2vfriswmgr
    sylan2
    expcom
    syl6bi
    syl
    a1d
    @23
    wn
    #
    @4
    @24
    @12
    @31
    cB
    cA
    cC
    ctp
    #
    cB
    cA
    cpr
    #
    wceq
    #
    @4
    @24
    @12
    wi
    #
    wi
    cB
    cA
    cC
    tpprceq3
    @34
    @4
    @2
    @35
    @34
    @3
    @1
    cV
    @34
    @3
    @33
    @1
    @34
    @3
    @33
    wceq
    @32
    @3
    @33
    cB
    cA
    cC
    tpcoma
    eqeq1i
    biimpi
    cB
    cA
    prcom
    syl6eq
    eqeq2d
    @2
    @12
    @24
    @6
    @2
    @10
    @2
    @6
    @11
    @10
    @17
    @13
    sylan2
    expcom
    a1d
    syl6bi
    syl
    com23
    @20
    @23
    wa
    #
    @24
    @4
    @6
    @10
    @36
    @24
    wa
    #
    @4
    wa
    #
    @6
    wa
    #
    @6
    @18
    @21
    w3a
    #
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    @24
    w3a
    #
    @4
    @10
    @39
    @6
    @18
    @21
    wa
    #
    wa
    @40
    @39
    @44
    @6
    @38
    @44
    @6
    @36
    @44
    @24
    @4
    @20
    @18
    @23
    @21
    @18
    @19
    simpl
    @21
    @22
    simpl
    anim12i
    ad2antrr
    anim1i
    ancomd
    @6
    @18
    @21
    3anass
    sylibr
    @37
    @43
    @4
    @6
    @37
    @41
    @42
    wa
    #
    @24
    wa
    @43
    @36
    @45
    @24
    @20
    @41
    @23
    @42
    @20
    cB
    cA
    @18
    @19
    simpr
    necomd
    @23
    cC
    cA
    @21
    @22
    simpr
    necomd
    anim12i
    anim1i
    @41
    @42
    @24
    df-3an
    sylibr
    ad2antrr
    @37
    @4
    @6
    simplr
    vw
    vv
    cA
    cB
    cC
    vh
    cE
    cG
    cV
    cX
    cvv
    cvv
    3vfriswmgr.v
    3vfriswmgr.e
    3vfriswmgr
    syl3anc
    exp41
    ecase
    pm2.61ine
    jaoi
    sylbi
    impcom
end
