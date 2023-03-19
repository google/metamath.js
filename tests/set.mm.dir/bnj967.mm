include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "w3a.mm"
include "com.mm"
include "cfv.mm"
include "w-bnj17.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "cvv.mm"
include "wfn.mm"
include "3adant3.mm"
include "bnj1235.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "simp23.mm"
include "simp3.mm"
include "3ad2ant3.mm"
include "bnj951.mm"
include "bnj923.mm"
include "bnj769.mm"
include "bnj240.mm"
include "wtr.mm"
include "word.mm"
include "nnord.mm"
include "ordtr.mm"
include "syl.mm"
include "trsuc.mm"
include "sylan.mm"
include "bnj658.mm"
include "anim1i.mm"
include "df-bnj17.mm"
include "sylibr.mm"
include "syl2anc.mm"
include "bnj945.mm"
include "3simpb.mm"
include "bnj1254.mm"
include "bnj958.mm"
include "bnj953.mm"

theorem bnj967
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
  assume bnj967.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj967.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj967.10: |- D = ( _om \ { (/) } )
  assume bnj967.12: |- C = U_ y e. ( f ` m ) _pred ( y , A , R )
  assume bnj967.13: |- G = ( f u. { <. n , C >. } )
  assume bnj967.44: |- ( ( ( R _FrSe A /\ X e. A ) /\ ( ch /\ n = suc m /\ p = suc n ) ) -> C e. _V )

  disjoint f y
  disjoint i y
  disjoint n y
  assert |- ( ( ( R _FrSe A /\ X e. A ) /\ ( ch /\ n = suc m /\ p = suc n ) /\ ( i e. _om /\ suc i e. p /\ suc i e. n ) ) -> ( G ` suc i ) = U_ y e. ( G ` i ) _pred ( y , A , R ) )

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
    csuc
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
    @6
    csuc
    #
    @3
    wcel
    #
    @8
    @1
    wcel
    #
    w3a
    #
    w3a
    #
    @6
    cG
    cfv
    #
    @6
    vf
    cv
    #
    cfv
    wceq
    #
    @8
    cG
    cfv
    #
    @8
    @14
    cfv
    wceq
    #
    @7
    @10
    wa
    #
    wps
    w-bnj17
    @16
    vy
    @13
    cA
    cR
    vy
    cv
    c-bnj14
    ciun
    wceq
    @15
    @17
    @18
    wps
    @12
    @12
    cC
    cvv
    wcel
    #
    @14
    @1
    wfn
    #
    @4
    @6
    @1
    wcel
    #
    w-bnj17
    #
    @15
    @12
    @19
    @20
    @4
    @10
    w-bnj17
    #
    @21
    @22
    @19
    @20
    @4
    @10
    @12
    @0
    @5
    @19
    @11
    bnj967.44
    3adant3
    @5
    @0
    @20
    @11
    wch
    @2
    @20
    @4
    wch
    @1
    cD
    wcel
    #
    @20
    wph
    wps
    bnj967.3
    bnj1235
    3ad2ant1
    3ad2ant2
    @0
    wch
    @2
    @4
    @11
    simp23
    @11
    @0
    @10
    @5
    @7
    @9
    @10
    simp3
    #
    3ad2ant3
    bnj951
    #
    @12
    @1
    com
    wcel
    #
    @10
    wa
    @21
    @0
    @5
    @11
    @27
    @10
    wch
    @2
    @27
    @4
    @24
    @20
    wph
    wps
    @27
    wch
    bnj967.3
    cD
    vn
    bnj967.10
    bnj923
    bnj769
    3ad2ant1
    @25
    bnj240
    @27
    @1
    wtr
    #
    @10
    @21
    @27
    @1
    word
    @28
    @1
    nnord
    @1
    ordtr
    syl
    @1
    @6
    trsuc
    sylan
    syl
    @23
    @21
    wa
    @19
    @20
    @4
    w3a
    #
    @21
    wa
    @22
    @23
    @29
    @21
    @19
    @20
    @4
    @10
    bnj658
    anim1i
    @19
    @20
    @4
    @21
    df-bnj17
    sylibr
    syl2anc
    @6
    cC
    vf
    vn
    cG
    vp
    bnj967.13
    bnj945
    syl
    @12
    @23
    @17
    @26
    @8
    cC
    vf
    vn
    cG
    vp
    bnj967.13
    bnj945
    syl
    @11
    @0
    @18
    @5
    @7
    @9
    @10
    3simpb
    3ad2ant3
    @5
    @0
    wps
    @11
    wch
    @2
    wps
    @4
    wch
    @24
    @20
    wph
    wps
    bnj967.3
    bnj1254
    3ad2ant1
    3ad2ant2
    bnj951
    wps
    vy
    cA
    cR
    vf
    vi
    vn
    cG
    bnj967.2
    vy
    cA
    cC
    cR
    vf
    vi
    vm
    vn
    cG
    bnj967.12
    bnj967.13
    bnj958
    bnj953
    syl
end
