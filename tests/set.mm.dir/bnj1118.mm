include "cv.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "wcel.mm"
include "csuc.mm"
include "wceq.mm"
include "cfv.mm"
include "wss.mm"
include "wi.mm"
include "bnj1110.mm"
include "ancl.mm"
include "bnj101.mm"
include "com.mm"
include "w-bnj17.mm"
include "w-bnj19.mm"
include "simpr2.mm"
include "wfn.mm"
include "bnj1254.mm"
include "3ad2ant3.mm"
include "ad2antrl.mm"
include "adantr.mm"
include "bnj1232.mm"
include "simpr1.mm"
include "bnj923.mm"
include "anim1i.mm"
include "ancomd.mm"
include "syl2anc.mm"
include "elnn.mm"
include "syl.mm"
include "cdm.mm"
include "adantl.mm"
include "ad2antlr.mm"
include "bnj951.mm"
include "cvv.mm"
include "c-bnj14.mm"
include "simp2bi.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "anim12i.mm"
include "ciun.mm"
include "bnj256.mm"
include "wal.mm"
include "bnj1112.mm"
include "biimpi.mm"
include "19.21bi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "syl5ibr.mm"
include "imp31.mm"
include "sylbi.mm"
include "wral.mm"
include "df-bnj19.mm"
include "ssralv.mm"
include "syl5bi.mm"
include "impcom.mm"
include "iunss.mm"
include "sylibr.mm"
include "sseq1.mm"
include "biimpar.mm"
include "syl2an.mm"
include "bnj1023.mm"

theorem bnj1118
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wsi: wff si
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cK: class K
  let cX: class X
  let bnjwetm: wff et'
  let bnjwph0: wff ph0
  assume bnj1118.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1118.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1118.5: |- ( ta <-> ( B e. _V /\ _TrFo ( B , A , R ) /\ _pred ( X , A , R ) C_ B ) )
  assume bnj1118.7: |- D = ( _om \ { (/) } )
  assume bnj1118.18: |- ( si <-> ( ( j e. n /\ j _E i ) -> et' ) )
  assume bnj1118.19: |- ( ph0 <-> ( i e. n /\ si /\ f e. K /\ i e. dom f ) )
  assume bnj1118.26: |- ( et' <-> ( ( f e. K /\ j e. dom f ) -> ( f ` j ) C_ B ) )

  disjoint A i
  disjoint A j
  disjoint A y
  disjoint i j
  disjoint i y
  disjoint j y
  disjoint B y
  disjoint D j
  disjoint R i
  disjoint R j
  disjoint R y
  disjoint f i
  disjoint f j
  disjoint f y
  disjoint i n
  disjoint j n
  assert |- E. j ( ( i =/= (/) /\ ( ( th /\ ta /\ ch ) /\ ph0 ) ) -> ( f ` i ) C_ B )

  proof
    vi
    cv
    #
    c0
    wne
    #
    wth
    wta
    wch
    w3a
    #
    bnjwph0
    wa
    #
    wa
    #
    @4
    vj
    cv
    #
    vn
    cv
    #
    wcel
    #
    @0
    @5
    csuc
    #
    wceq
    #
    @5
    vf
    cv
    #
    cfv
    #
    cB
    wss
    #
    w3a
    #
    wa
    #
    @0
    @10
    cfv
    #
    cB
    wss
    #
    vj
    @4
    @13
    wi
    @4
    @14
    wi
    vj
    wph
    wps
    wch
    wth
    wta
    wsi
    cB
    cD
    vf
    vi
    vj
    vn
    cK
    bnjwetm
    bnjwph0
    bnj1118.3
    bnj1118.7
    bnj1118.18
    bnj1118.19
    bnj1118.26
    bnj1110
    @4
    @13
    ancl
    bnj101
    @14
    @9
    wps
    @5
    com
    wcel
    #
    @0
    @6
    wcel
    #
    w-bnj17
    #
    cA
    cB
    cR
    w-bnj19
    #
    @12
    wa
    #
    @16
    @9
    wps
    @17
    @18
    @14
    @4
    @7
    @9
    @12
    simpr2
    @4
    wps
    @13
    @2
    wps
    @1
    bnjwph0
    wch
    wth
    wps
    wta
    wch
    @6
    cD
    wcel
    #
    @10
    @6
    wfn
    #
    wph
    wps
    bnj1118.3
    bnj1254
    3ad2ant3
    ad2antrl
    adantr
    @14
    @7
    @6
    com
    wcel
    #
    wa
    #
    @17
    @14
    @22
    @7
    @25
    @4
    @22
    @13
    @2
    @22
    @1
    bnjwph0
    wch
    wth
    @22
    wta
    wch
    @22
    @23
    wph
    wps
    bnj1118.3
    bnj1232
    3ad2ant3
    ad2antrl
    adantr
    @4
    @7
    @9
    @12
    simpr1
    @22
    @7
    wa
    @24
    @7
    @22
    @24
    @7
    cD
    vn
    bnj1118.7
    bnj923
    anim1i
    ancomd
    syl2anc
    @5
    @6
    elnn
    syl
    @3
    @18
    @1
    @13
    bnjwph0
    @18
    @2
    bnjwph0
    @18
    wsi
    @10
    cK
    wcel
    @0
    @10
    cdm
    wcel
    bnj1118.19
    bnj1232
    adantl
    ad2antlr
    bnj951
    @4
    @20
    @13
    @12
    @2
    @20
    @1
    bnjwph0
    wta
    wth
    @20
    wch
    wta
    cB
    cvv
    wcel
    @20
    cA
    cR
    cX
    c-bnj14
    cB
    wss
    bnj1118.5
    simp2bi
    3ad2ant2
    ad2antrl
    @7
    @9
    @12
    simp3
    anim12i
    @19
    @15
    vy
    @11
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
    @27
    cB
    wss
    #
    @16
    @21
    @19
    @9
    wps
    wa
    @17
    @18
    wa
    #
    wa
    @28
    @9
    wps
    @17
    @18
    bnj256
    @9
    wps
    @30
    @28
    wps
    @30
    @28
    wi
    @9
    @17
    @8
    @6
    wcel
    #
    wa
    #
    @8
    @10
    cfv
    #
    @27
    wceq
    #
    wi
    #
    wps
    @35
    vj
    wps
    @35
    vj
    wal
    wps
    vy
    cA
    cR
    vf
    vi
    vj
    vn
    bnj1118.2
    bnj1112
    biimpi
    19.21bi
    @9
    @30
    @32
    @28
    @34
    @9
    @18
    @31
    @17
    @0
    @8
    @6
    eleq1
    anbi2d
    @9
    @15
    @33
    @27
    @0
    @8
    @10
    fveq2
    eqeq1d
    imbi12d
    syl5ibr
    imp31
    sylbi
    @21
    @26
    cB
    wss
    #
    vy
    @11
    wral
    #
    @29
    @12
    @20
    @37
    @20
    @36
    vy
    cB
    wral
    @12
    @37
    vy
    cA
    cB
    cR
    df-bnj19
    @36
    vy
    @11
    cB
    ssralv
    syl5bi
    impcom
    vy
    @11
    @26
    cB
    iunss
    sylibr
    @28
    @16
    @29
    @15
    @27
    cB
    sseq1
    biimpar
    syl2an
    syl2anc
    bnj1023
end
