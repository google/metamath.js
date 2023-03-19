include "ccnv.mm"
include "cpred.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "wrex.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "wwe.mm"
include "wse.mm"
include "wss.mm"
include "wne.mm"
include "predss.mm"
include "a1i.mm"
include "crab.mm"
include "wcel.mm"
include "dfpred3g.mm"
include "syl.mm"
include "cvv.mm"
include "elexd.mm"
include "rabn0.mm"
include "wb.mm"
include "brcnvg.mm"
include "ancoms.mm"
include "rexbidva.mm"
include "syl5bb.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "eqnetrd.mm"
include "tz6.26.mm"
include "syl22anc.mm"
include "rexeqdv.mm"
include "breq1.mm"
include "rexrab.mm"
include "w3a.mm"
include "noel.mm"
include "simp2r.mm"
include "eleq2d.mm"
include "mtbiri.mm"
include "vex.mm"
include "simp3.mm"
include "elpredg.mm"
include "mtbid.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "expr.mm"
include "simp1rl.mm"
include "simp1rr.mm"
include "adantr.mm"
include "3ad2ant1.mm"
include "elpred.mm"
include "mpbir2and.mm"
include "rspcev.mm"
include "3expia.mm"
include "anim12d.mm"
include "ancomsd.mm"
include "reximdva.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "mpd.mm"

theorem wsuclem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cR: class R
  let cV: class V
  let cX: class X
  assume wsuclem.1: |- ( ph -> R We A )
  assume wsuclem.2: |- ( ph -> R Se A )
  assume wsuclem.3: |- ( ph -> X e. V )
  assume wsuclem.4: |- ( ph -> E. w e. A X R w )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint R w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint X w
  assert |- ( ph -> E. x e. A ( A. y e. Pred ( `' R , A , X ) -. y R x /\ A. y e. A ( x R y -> E. z e. Pred ( `' R , A , X ) z R y ) ) )

  proof
    wph
    cA
    cR
    ccnv
    #
    cX
    cpred
    #
    cR
    vx
    cv
    #
    cpred
    #
    c0
    wceq
    #
    vx
    @1
    wrex
    #
    vy
    cv
    #
    @2
    cR
    wbr
    #
    wn
    #
    vy
    @1
    wral
    #
    @2
    @6
    cR
    wbr
    #
    vz
    cv
    #
    @6
    cR
    wbr
    #
    vz
    @1
    wrex
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    wrex
    #
    wph
    cA
    cR
    wwe
    cA
    cR
    wse
    @1
    cA
    wss
    #
    @1
    c0
    wne
    @5
    wsuclem.1
    wsuclem.2
    @18
    wph
    cA
    @0
    cX
    predss
    a1i
    wph
    @1
    vw
    cv
    #
    cX
    @0
    wbr
    #
    vw
    cA
    crab
    #
    c0
    wph
    cX
    cV
    wcel
    #
    @1
    @21
    wceq
    wsuclem.3
    vw
    cA
    @0
    cV
    cX
    dfpred3g
    syl
    wph
    cX
    cvv
    wcel
    #
    cX
    @19
    cR
    wbr
    #
    vw
    cA
    wrex
    #
    @21
    c0
    wne
    #
    wph
    cX
    cV
    wsuclem.3
    elexd
    wsuclem.4
    @23
    @26
    @25
    @26
    @20
    vw
    cA
    wrex
    @23
    @25
    @20
    vw
    cA
    rabn0
    @23
    @20
    @24
    vw
    cA
    @19
    cA
    wcel
    @23
    @20
    @24
    wb
    @19
    cX
    cA
    cvv
    cR
    brcnvg
    ancoms
    rexbidva
    syl5bb
    biimpar
    syl2anc
    eqnetrd
    vx
    cA
    @1
    cR
    tz6.26
    syl22anc
    wph
    @5
    @4
    vx
    @6
    cX
    @0
    wbr
    #
    vy
    cA
    crab
    #
    wrex
    #
    @17
    wph
    @4
    vx
    @1
    @28
    wph
    @22
    @1
    @28
    wceq
    wsuclem.3
    vy
    cA
    @0
    cV
    cX
    dfpred3g
    syl
    rexeqdv
    @29
    @2
    cX
    @0
    wbr
    #
    @4
    wa
    #
    vx
    cA
    wrex
    wph
    @17
    @27
    @30
    @4
    vx
    vy
    cA
    @6
    @2
    cX
    @0
    breq1
    rexrab
    wph
    @31
    @16
    vx
    cA
    wph
    @2
    cA
    wcel
    #
    wa
    #
    @4
    @30
    @16
    @33
    @4
    @9
    @30
    @15
    wph
    @32
    @4
    @9
    wph
    @32
    @4
    wa
    #
    wa
    @8
    vy
    @1
    wph
    @34
    @6
    @1
    wcel
    #
    @8
    wph
    @34
    @35
    w3a
    #
    @6
    @3
    wcel
    #
    @7
    @36
    @37
    @6
    c0
    wcel
    @6
    noel
    @36
    @3
    c0
    @6
    wph
    @32
    @4
    @35
    simp2r
    eleq2d
    mtbiri
    @36
    @2
    cvv
    wcel
    #
    @35
    @37
    @7
    wb
    @38
    @36
    vx
    vex
    #
    a1i
    wph
    @34
    @35
    simp3
    @1
    cvv
    cR
    @2
    @6
    elpredg
    syl2anc
    mtbid
    3expa
    ralrimiva
    expr
    wph
    @32
    @30
    @15
    wph
    @32
    @30
    wa
    #
    wa
    #
    @14
    vy
    cA
    @41
    @6
    cA
    wcel
    #
    @10
    @13
    @41
    @42
    @10
    w3a
    #
    @2
    @1
    wcel
    #
    @10
    @13
    @43
    @44
    @32
    @30
    @32
    @30
    wph
    @42
    @10
    simp1rl
    @32
    @30
    wph
    @42
    @10
    simp1rr
    @43
    @22
    @44
    @40
    wb
    @41
    @42
    @22
    @10
    wph
    @22
    @40
    wsuclem.3
    adantr
    3ad2ant1
    cA
    cV
    @0
    cX
    @2
    @39
    elpred
    syl
    mpbir2and
    @41
    @42
    @10
    simp3
    @12
    @10
    vz
    @2
    @1
    @11
    @2
    @6
    cR
    breq1
    rspcev
    syl2anc
    3expia
    ralrimiva
    expr
    anim12d
    ancomsd
    reximdva
    syl5bi
    sylbid
    mpd
end
