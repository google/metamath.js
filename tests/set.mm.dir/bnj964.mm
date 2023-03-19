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
include "wi.mm"
include "wal.mm"
include "nfv.mm"
include "wfn.mm"
include "bnj1095.mm"
include "bnj1096.mm"
include "nf5i.mm"
include "nf3an.mm"
include "nfan.mm"
include "w-bnj17.mm"
include "bnj255.mm"
include "wo.mm"
include "bnj645.mm"
include "simp3.mm"
include "bnj706.mm"
include "eleq2.mm"
include "biimpac.mm"
include "elsuci.mm"
include "eqcom.mm"
include "orbi2i.mm"
include "sylib.mm"
include "syl.mm"
include "syl2anc.mm"
include "df-3an.mm"
include "3anbi3i.mm"
include "bitr4i.mm"
include "bnj345.mm"
include "bnj252.mm"
include "3bitri.mm"
include "anbi2i.mm"
include "sylbir.mm"
include "ex.mm"
include "jaoi.mm"
include "mpcom.mm"
include "3expia.mm"
include "alrimi.mm"
include "vex.mm"
include "bnj539.mm"
include "bnj965.mm"
include "bnj115.mm"
include "sylibr.mm"

theorem bnj964
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
  let bnjwpsm: wff ps'
  let bnjwpsn: wff ps"
  assume bnj964.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj964.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj964.5: |- ( ps' <-> [. p / n ]. ps )
  assume bnj964.8: |- ( ps" <-> [. G / f ]. ps' )
  assume bnj964.12: |- C = U_ y e. ( f ` m ) _pred ( y , A , R )
  assume bnj964.13: |- G = ( f u. { <. n , C >. } )
  assume bnj964.96: |- ( ( ( R _FrSe A /\ X e. A ) /\ ( ch /\ n = suc m /\ p = suc n ) /\ ( i e. _om /\ suc i e. p /\ suc i e. n ) ) -> ( G ` suc i ) = U_ y e. ( G ` i ) _pred ( y , A , R ) )
  assume bnj964.165: |- ( ( ( R _FrSe A /\ X e. A ) /\ ( ch /\ n = suc m /\ p = suc n ) /\ ( i e. _om /\ suc i e. p /\ n = suc i ) ) -> ( G ` suc i ) = U_ y e. ( G ` i ) _pred ( y , A , R ) )

  disjoint A f
  disjoint A i
  disjoint A n
  disjoint f i
  disjoint f n
  disjoint i n
  disjoint D i
  disjoint G i
  disjoint R f
  disjoint R i
  disjoint R n
  disjoint X i
  disjoint f p
  disjoint i p
  disjoint f y
  disjoint i y
  disjoint n y
  disjoint i m
  disjoint i ph
  assert |- ( ( ( R _FrSe A /\ X e. A ) /\ ( ch /\ n = suc m /\ p = suc n ) ) -> ps" )

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
    #
    wceq
    #
    w3a
    #
    wa
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
    @3
    wcel
    #
    wa
    #
    @10
    cG
    cfv
    vy
    @8
    cG
    cfv
    cA
    cR
    vy
    cv
    c-bnj14
    #
    ciun
    wceq
    #
    wi
    #
    vi
    wal
    bnjwpsn
    @7
    @15
    vi
    @0
    @6
    vi
    @0
    vi
    nfv
    wch
    @2
    @5
    vi
    wch
    vi
    wps
    wch
    @1
    cD
    wcel
    vf
    cv
    #
    @1
    wfn
    wph
    vi
    wps
    @10
    @1
    wcel
    #
    @10
    @16
    cfv
    vy
    @8
    @16
    cfv
    @13
    ciun
    wceq
    wi
    vi
    com
    bnj964.2
    bnj1095
    bnj964.3
    bnj1096
    nf5i
    @2
    vi
    nfv
    @5
    vi
    nfv
    nf3an
    nfan
    @0
    @6
    @12
    @14
    @0
    @6
    @12
    w3a
    #
    @0
    @6
    @9
    @11
    w-bnj17
    #
    @14
    @0
    @6
    @9
    @11
    bnj255
    #
    @17
    @1
    @10
    wceq
    #
    wo
    #
    @19
    @14
    @19
    @11
    @5
    @22
    @0
    @6
    @9
    @11
    bnj645
    @0
    @6
    @9
    @11
    @5
    wch
    @2
    @5
    simp3
    bnj706
    @11
    @5
    wa
    @10
    @4
    wcel
    #
    @22
    @5
    @11
    @23
    @3
    @4
    @10
    eleq2
    biimpac
    @23
    @17
    @10
    @1
    wceq
    #
    wo
    @22
    @10
    @1
    elsuci
    @24
    @21
    @17
    @10
    @1
    eqcom
    orbi2i
    sylib
    syl
    syl2anc
    @17
    @19
    @14
    wi
    @21
    @17
    @19
    @14
    @17
    @19
    wa
    #
    @0
    @6
    @9
    @11
    @17
    w3a
    #
    w3a
    #
    @14
    @27
    @17
    @18
    wa
    #
    @25
    @27
    @0
    @6
    @12
    @17
    w-bnj17
    #
    @17
    @0
    @6
    @12
    w-bnj17
    @28
    @27
    @0
    @6
    @12
    @17
    wa
    #
    w3a
    @29
    @26
    @30
    @0
    @6
    @9
    @11
    @17
    df-3an
    3anbi3i
    @0
    @6
    @12
    @17
    bnj255
    bitr4i
    @0
    @6
    @12
    @17
    bnj345
    @17
    @0
    @6
    @12
    bnj252
    3bitri
    @19
    @18
    @17
    @20
    anbi2i
    bitr4i
    bnj964.96
    sylbir
    ex
    @21
    @19
    @14
    @21
    @19
    wa
    #
    @0
    @6
    @9
    @11
    @21
    w3a
    #
    w3a
    #
    @14
    @33
    @21
    @18
    wa
    #
    @31
    @33
    @0
    @6
    @12
    @21
    w-bnj17
    #
    @21
    @0
    @6
    @12
    w-bnj17
    @34
    @33
    @0
    @6
    @12
    @21
    wa
    #
    w3a
    @35
    @32
    @36
    @0
    @6
    @9
    @11
    @21
    df-3an
    3anbi3i
    @0
    @6
    @12
    @21
    bnj255
    bitr4i
    @0
    @6
    @12
    @21
    bnj345
    @21
    @0
    @6
    @12
    bnj252
    3bitri
    @19
    @18
    @21
    @20
    anbi2i
    bitr4i
    bnj964.165
    sylbir
    ex
    jaoi
    mpcom
    sylbir
    3expia
    alrimi
    @14
    @11
    bnjwpsn
    com
    vi
    bnjwpsm
    vy
    cA
    cC
    cR
    vf
    vi
    vm
    vn
    cG
    @3
    bnjwpsn
    wps
    vy
    cA
    cR
    vi
    vn
    @16
    @3
    bnjwpsm
    bnj964.2
    bnj964.5
    vp
    vex
    bnj539
    bnj964.8
    bnj964.12
    bnj964.13
    bnj965
    bnj115
    sylibr
end
