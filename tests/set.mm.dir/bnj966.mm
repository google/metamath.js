include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "w3a.mm"
include "com.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wfun.mm"
include "cop.mm"
include "bnj930.mm"
include "3adant3.mm"
include "csn.mm"
include "cun.mm"
include "opex.mm"
include "snid.mm"
include "elun2.mm"
include "ax-mp.mm"
include "eleqtrri.mm"
include "funopfv.mm"
include "mpisyl.mm"
include "wb.mm"
include "simp22.mm"
include "simp33.mm"
include "bnj551.mm"
include "syl2anc.mm"
include "suceq.mm"
include "eqeq2d.mm"
include "biimpac.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "bnj1113.mm"
include "syl5eq.mm"
include "adantl.mm"
include "eqeq12d.mm"
include "mpbid.mm"
include "cvv.mm"
include "wfn.mm"
include "w-bnj17.mm"
include "bnj1235.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "simp23.mm"
include "bnj951.mm"
include "bnj923.mm"
include "bnj769.mm"
include "simp3.mm"
include "bnj240.mm"
include "vex.mm"
include "bnj216.mm"
include "syl.mm"
include "bnj658.mm"
include "anim1i.mm"
include "df-bnj17.mm"
include "sylibr.mm"
include "bnj945.mm"
include "bnj958.mm"
include "bnj956.mm"
include "mpbird.mm"

theorem bnj966
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cX: class X
  let vp: setvar p
  assume bnj966.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj966.10: |- D = ( _om \ { (/) } )
  assume bnj966.12: |- C = U_ y e. ( f ` m ) _pred ( y , A , R )
  assume bnj966.13: |- G = ( f u. { <. n , C >. } )
  assume bnj966.44: |- ( ( ( R _FrSe A /\ X e. A ) /\ ( ch /\ n = suc m /\ p = suc n ) ) -> C e. _V )
  assume bnj966.53: |- ( ( ( R _FrSe A /\ X e. A ) /\ ( ch /\ n = suc m /\ p = suc n ) ) -> G Fn p )

  disjoint f y
  disjoint i y
  disjoint m y
  disjoint n y
  assert |- ( ( ( R _FrSe A /\ X e. A ) /\ ( ch /\ n = suc m /\ p = suc n ) /\ ( i e. _om /\ suc i e. p /\ n = suc i ) ) -> ( G ` suc i ) = U_ y e. ( G ` i ) _pred ( y , A , R ) )

  proof
    cA
    cR
    w-bnj15
    cX
    cA
    wcel
    wa
    #
    wch
    vn
    cv
    #
    vm
    cv
    #
    csuc
    #
    wceq
    #
    vp
    cv
    #
    @1
    csuc
    wceq
    #
    w3a
    #
    vi
    cv
    #
    com
    wcel
    #
    @8
    csuc
    #
    @5
    wcel
    #
    @1
    @10
    wceq
    #
    w3a
    #
    w3a
    #
    @10
    cG
    cfv
    #
    vy
    @8
    cG
    cfv
    #
    cA
    cR
    vy
    cv
    c-bnj14
    #
    ciun
    #
    wceq
    #
    @15
    vy
    @8
    vf
    cv
    #
    cfv
    #
    @17
    ciun
    #
    wceq
    #
    @14
    @1
    cG
    cfv
    #
    cC
    wceq
    #
    @23
    @14
    cG
    wfun
    #
    @1
    cC
    cop
    #
    cG
    wcel
    @25
    @0
    @7
    @26
    @13
    @0
    @7
    wa
    @5
    cG
    bnj966.53
    bnj930
    3adant3
    @27
    @20
    @27
    csn
    #
    cun
    #
    cG
    @27
    @28
    wcel
    @27
    @29
    wcel
    @27
    @1
    cC
    opex
    snid
    @27
    @28
    @20
    elun2
    ax-mp
    bnj966.13
    eleqtrri
    @1
    cC
    cG
    funopfv
    mpisyl
    @14
    @4
    @2
    @8
    wceq
    #
    @25
    @23
    wb
    @0
    wch
    @4
    @6
    @13
    simp22
    #
    @14
    @4
    @12
    @30
    @31
    @0
    @7
    @9
    @11
    @12
    simp33
    #
    vi
    vn
    vm
    bnj551
    syl2anc
    @4
    @30
    wa
    #
    @24
    @15
    cC
    @22
    @33
    @1
    @10
    cG
    @30
    @4
    @12
    @30
    @3
    @10
    @1
    @2
    @8
    suceq
    eqeq2d
    biimpac
    fveq2d
    @30
    cC
    @22
    wceq
    @4
    @30
    cC
    vy
    @2
    @20
    cfv
    #
    @17
    ciun
    @22
    bnj966.12
    vy
    @2
    @8
    @34
    @21
    @17
    @2
    @8
    @20
    fveq2
    bnj1113
    syl5eq
    adantl
    eqeq12d
    syl2anc
    mpbid
    @14
    @16
    @21
    wceq
    #
    @19
    @23
    wb
    @14
    cC
    cvv
    wcel
    #
    @20
    @1
    wfn
    #
    @6
    @12
    w-bnj17
    #
    @8
    @1
    wcel
    #
    @35
    @36
    @37
    @6
    @12
    @14
    @0
    @7
    @36
    @13
    bnj966.44
    3adant3
    @7
    @0
    @37
    @13
    wch
    @4
    @37
    @6
    wch
    @1
    cD
    wcel
    #
    @37
    wph
    wps
    bnj966.3
    bnj1235
    3ad2ant1
    3ad2ant2
    @0
    wch
    @4
    @6
    @13
    simp23
    @32
    bnj951
    @14
    @1
    com
    wcel
    #
    @12
    wa
    @39
    @0
    @7
    @13
    @41
    @12
    wch
    @4
    @41
    @6
    @40
    @37
    wph
    wps
    @41
    wch
    bnj966.3
    cD
    vn
    bnj966.10
    bnj923
    bnj769
    3ad2ant1
    @9
    @11
    @12
    simp3
    bnj240
    @12
    @39
    @41
    @1
    @8
    vi
    vex
    bnj216
    adantl
    syl
    @38
    @39
    wa
    #
    @36
    @37
    @6
    @39
    w-bnj17
    #
    @35
    @42
    @36
    @37
    @6
    w3a
    #
    @39
    wa
    @43
    @38
    @44
    @39
    @36
    @37
    @6
    @12
    bnj658
    anim1i
    @36
    @37
    @6
    @39
    df-bnj17
    sylibr
    @8
    cC
    vf
    vn
    cG
    vp
    bnj966.13
    bnj945
    syl
    syl2anc
    @35
    @18
    @22
    @15
    vy
    @16
    @21
    @17
    vy
    cA
    cC
    cR
    vf
    vi
    vm
    vn
    cG
    bnj966.12
    bnj966.13
    bnj958
    bnj956
    eqeq2d
    syl
    mpbird
end
