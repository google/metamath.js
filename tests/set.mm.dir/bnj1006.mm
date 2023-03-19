include "w-bnj17.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "c-bnj14.mm"
include "csuc.mm"
include "wss.mm"
include "wel.mm"
include "simprbi.mm"
include "bnj708.mm"
include "cvv.mm"
include "wfn.mm"
include "wceq.mm"
include "w-bnj15.mm"
include "wa.mm"
include "w3a.mm"
include "c-bnj18.mm"
include "bnj253.mm"
include "simp1bi.mm"
include "sylbi.mm"
include "bnj705.mm"
include "bnj643.mm"
include "com.mm"
include "3simpc.mm"
include "bnj707.mm"
include "3anass.mm"
include "sylanbrc.mm"
include "biid.mm"
include "bnj969.mm"
include "syl2anc.mm"
include "bnj1235.mm"
include "bnj706.mm"
include "simp3bi.mm"
include "simplbi.mm"
include "bnj951.mm"
include "bnj945.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "anim1i.mm"
include "df-bnj17.mm"
include "sylibr.mm"
include "bnj999.mm"
include "mpdan.mm"

theorem bnj1006
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vy: setvar y
  let vz: setvar z
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
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  let bnjwphn: wff ph"
  let bnjwpsn: wff ps"
  let bnjwchn: wff ch"
  assume bnj1006.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj1006.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1006.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1006.4: |- ( th <-> ( R _FrSe A /\ X e. A /\ y e. _trCl ( X , A , R ) /\ z e. _pred ( y , A , R ) ) )
  assume bnj1006.5: |- ( ta <-> ( m e. _om /\ n = suc m /\ p = suc n ) )
  assume bnj1006.6: |- ( et <-> ( i e. n /\ y e. ( f ` i ) ) )
  assume bnj1006.7: |- ( ph' <-> [. p / n ]. ph )
  assume bnj1006.8: |- ( ps' <-> [. p / n ]. ps )
  assume bnj1006.9: |- ( ch' <-> [. p / n ]. ch )
  assume bnj1006.10: |- ( ph" <-> [. G / f ]. ph' )
  assume bnj1006.11: |- ( ps" <-> [. G / f ]. ps' )
  assume bnj1006.12: |- ( ch" <-> [. G / f ]. ch' )
  assume bnj1006.13: |- D = ( _om \ { (/) } )
  assume bnj1006.15: |- C = U_ y e. ( f ` m ) _pred ( y , A , R )
  assume bnj1006.16: |- G = ( f u. { <. n , C >. } )
  assume bnj1006.28: |- ( ( th /\ ch /\ ta /\ et ) -> ( ch" /\ i e. _om /\ suc i e. p ) )

  disjoint A f
  disjoint A i
  disjoint A m
  disjoint A n
  disjoint A y
  disjoint f i
  disjoint f m
  disjoint f n
  disjoint f y
  disjoint i m
  disjoint i n
  disjoint i y
  disjoint m n
  disjoint m y
  disjoint n y
  disjoint D f
  disjoint D n
  disjoint G i
  disjoint R f
  disjoint R i
  disjoint R m
  disjoint R n
  disjoint R y
  disjoint X f
  disjoint X n
  disjoint f p
  disjoint i p
  disjoint n p
  assert |- ( ( th /\ ch /\ ta /\ et ) -> _pred ( y , A , R ) C_ ( G ` suc i ) )

  proof
    wth
    wch
    wta
    wet
    w-bnj17
    #
    vy
    cv
    #
    vi
    cv
    #
    cG
    cfv
    #
    wcel
    #
    cA
    cR
    @1
    c-bnj14
    #
    @2
    csuc
    #
    cG
    cfv
    wss
    #
    @0
    @1
    @2
    vf
    cv
    #
    cfv
    #
    @3
    wth
    wch
    wta
    wet
    @1
    @9
    wcel
    #
    wet
    vi
    vn
    wel
    #
    @10
    bnj1006.6
    simprbi
    bnj708
    @0
    cC
    cvv
    wcel
    #
    @8
    vn
    cv
    #
    wfn
    #
    vp
    cv
    #
    @13
    csuc
    wceq
    #
    @11
    w-bnj17
    @3
    @9
    wceq
    @12
    @14
    @16
    @11
    @0
    @0
    cA
    cR
    w-bnj15
    #
    cX
    cA
    wcel
    #
    wa
    #
    wch
    @13
    vm
    cv
    #
    csuc
    wceq
    #
    @16
    w3a
    #
    @12
    wth
    wch
    wta
    wet
    @19
    wth
    @17
    @18
    @1
    cA
    cR
    cX
    c-bnj18
    wcel
    #
    vz
    cv
    @5
    wcel
    #
    w-bnj17
    #
    @19
    bnj1006.4
    @25
    @19
    @23
    @24
    @17
    @18
    @23
    @24
    bnj253
    simp1bi
    sylbi
    bnj705
    @0
    wch
    @21
    @16
    wa
    #
    @22
    wth
    wch
    wta
    wet
    bnj643
    wth
    wch
    wta
    wet
    @26
    wta
    @20
    com
    wcel
    #
    @21
    @16
    w3a
    @26
    bnj1006.5
    @27
    @21
    @16
    3simpc
    sylbi
    bnj707
    wch
    @21
    @16
    3anass
    sylanbrc
    wph
    wps
    wch
    @14
    wph
    wps
    w3a
    #
    @13
    cD
    wcel
    #
    @16
    vm
    vn
    wel
    w3a
    #
    vy
    cA
    cC
    cD
    cR
    vf
    vi
    vm
    vn
    cX
    vp
    bnj1006.1
    bnj1006.2
    bnj1006.3
    bnj1006.13
    bnj1006.15
    @28
    biid
    @30
    biid
    bnj969
    syl2anc
    wth
    wch
    wta
    wet
    @14
    wch
    @29
    @14
    wph
    wps
    bnj1006.3
    bnj1235
    bnj706
    wth
    wch
    wta
    wet
    @16
    wta
    @27
    @21
    @16
    bnj1006.5
    simp3bi
    bnj707
    wth
    wch
    wta
    wet
    @11
    wet
    @11
    @10
    bnj1006.6
    simplbi
    bnj708
    bnj951
    @2
    cC
    vf
    vn
    cG
    vp
    bnj1006.16
    bnj945
    syl
    eleqtrrd
    @0
    @4
    wa
    #
    bnjwchn
    @2
    com
    wcel
    #
    @6
    @15
    wcel
    #
    @4
    w-bnj17
    #
    @7
    @31
    bnjwchn
    @32
    @33
    w3a
    #
    @4
    wa
    @34
    @0
    @35
    @4
    bnj1006.28
    anim1i
    bnjwchn
    @32
    @33
    @4
    df-bnj17
    sylibr
    wph
    wps
    wch
    vy
    cA
    cC
    cD
    cR
    vf
    vi
    vm
    vn
    cG
    cX
    vp
    bnjwphm
    bnjwpsm
    bnjwchm
    bnjwphn
    bnjwpsn
    bnjwchn
    bnj1006.1
    bnj1006.2
    bnj1006.3
    bnj1006.7
    bnj1006.8
    bnj1006.9
    bnj1006.10
    bnj1006.11
    bnj1006.12
    bnj1006.15
    bnj1006.16
    bnj999
    syl
    mpdan
end
