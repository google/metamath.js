include "wel.mm"
include "wa.mm"
include "wi.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "wfn.mm"
include "simp2bi.mm"
include "sylib.mm"
include "eqtr3.mm"
include "syl2an.mm"
include "3adant1.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "syl5ibr.mm"
include "sylibr.mm"
include "a1d.mm"
include "wne.mm"
include "w-bnj17.mm"
include "bnj253.mm"
include "bnj252.mm"
include "anidm.mm"
include "3anbi1i.mm"
include "3bitr3i.mm"
include "wex.mm"
include "csuc.mm"
include "df-bnj17.mm"
include "cep.mm"
include "wbr.mm"
include "wsbc.mm"
include "bnj1095.mm"
include "bnj1352.mm"
include "hbxfrbi.mm"
include "com.mm"
include "wrex.mm"
include "bnj170.mm"
include "bnj923.mm"
include "elnn.mm"
include "sylan2.mm"
include "anim1i.mm"
include "sylbi.mm"
include "nnsuc.mm"
include "rexex.mm"
include "3syl.mm"
include "bnj721.mm"
include "bnj596.mm"
include "bnj667.mm"
include "bnj258.mm"
include "ciun.mm"
include "bnj219.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "vex.mm"
include "bnj216.mm"
include "df-3an.mm"
include "3anrot.mm"
include "ancom.mm"
include "word.mm"
include "csn.mm"
include "cdif.mm"
include "eldifi.mm"
include "eleq2s.mm"
include "nnord.mm"
include "ordtr1.mm"
include "imp.mm"
include "syl3an3.mm"
include "wral.mm"
include "rsp.mm"
include "mpan9.mm"
include "mpd.mm"
include "bnj446.mm"
include "pm3.35.mm"
include "sylan2b.mm"
include "iuneq1.mm"
include "bnj658.mm"
include "simp3bi.mm"
include "bnj240.mm"
include "anim12i.mm"
include "simpl.mm"
include "anim2i.mm"
include "simp3.mm"
include "simpl1.mm"
include "bitri.mm"
include "bnj589.mm"
include "bnj590.mm"
include "syldan.mm"
include "simpr.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "syl.mm"
include "bnj593.mm"
include "19.9v.mm"
include "3imtr3i.mm"
include "expimpd.mm"
include "syl5bir.mm"
include "3expib.mm"
include "pm2.61ine.mm"

theorem bnj594
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  assume bnj594.1: |- ( ph <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj594.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj594.3: |- ( ch <-> ( f Fn n /\ ph /\ ps ) )
  assume bnj594.7: |- D = ( _om \ { (/) } )
  assume bnj594.9: |- ( ph' <-> ( g ` (/) ) = _pred ( x , A , R ) )
  assume bnj594.10: |- ( ps' <-> A. i e. _om ( suc i e. n -> ( g ` suc i ) = U_ y e. ( g ` i ) _pred ( y , A , R ) ) )
  assume bnj594.11: |- ( ch' <-> ( g Fn n /\ ph' /\ ps' ) )
  assume bnj594.15: |- ( th <-> ( ( n e. D /\ ch /\ ch' ) -> ( f ` j ) = ( g ` j ) ) )
  assume bnj594.16: |- ( [. k / j ]. th <-> ( ( n e. D /\ ch /\ ch' ) -> ( f ` k ) = ( g ` k ) ) )
  assume bnj594.17: |- ( ta <-> A. k e. n ( k _E j -> [. k / j ]. th ) )

  disjoint A i
  disjoint A k
  disjoint i k
  disjoint D k
  disjoint R i
  disjoint R k
  disjoint ch k
  disjoint ch' k
  disjoint f i
  disjoint f k
  disjoint f y
  disjoint i y
  disjoint k y
  disjoint g i
  disjoint g k
  disjoint g y
  disjoint i n
  disjoint k n
  disjoint j k
  assert |- ( ( j e. n /\ ta ) -> th )

  proof
    vj
    vn
    wel
    #
    wta
    wa
    #
    wth
    wi
    vj
    cv
    #
    c0
    @2
    c0
    wceq
    #
    wth
    @1
    @3
    vn
    cv
    #
    cD
    wcel
    #
    wch
    bnjwchm
    w3a
    #
    @2
    vf
    cv
    #
    cfv
    #
    @2
    vg
    cv
    #
    cfv
    #
    wceq
    #
    wi
    #
    wth
    @6
    @11
    @3
    c0
    @7
    cfv
    #
    c0
    @9
    cfv
    #
    wceq
    #
    wch
    bnjwchm
    @15
    @5
    wch
    @13
    cA
    cR
    vx
    cv
    c-bnj14
    #
    wceq
    #
    @14
    @16
    wceq
    #
    @15
    bnjwchm
    wch
    wph
    @17
    wch
    @7
    @4
    wfn
    #
    wph
    wps
    bnj594.3
    simp2bi
    bnj594.1
    sylib
    bnjwchm
    bnjwphm
    @18
    bnjwchm
    @9
    @4
    wfn
    #
    bnjwphm
    bnjwpsm
    bnj594.11
    simp2bi
    bnj594.9
    sylib
    @13
    @14
    @16
    eqtr3
    syl2an
    3adant1
    @3
    @8
    @13
    @10
    @14
    @2
    c0
    @7
    fveq2
    @2
    c0
    @9
    fveq2
    eqeq12d
    syl5ibr
    bnj594.15
    sylibr
    a1d
    @2
    c0
    wne
    #
    @0
    wta
    wth
    @21
    @0
    wta
    w3a
    #
    @12
    wth
    @6
    @5
    @6
    wa
    #
    @22
    @11
    @5
    @5
    wch
    bnjwchm
    w-bnj17
    @5
    @5
    wa
    #
    wch
    bnjwchm
    w3a
    @23
    @6
    @5
    @5
    wch
    bnjwchm
    bnj253
    @5
    @5
    wch
    bnjwchm
    bnj252
    @24
    @5
    wch
    bnjwchm
    @5
    anidm
    3anbi1i
    3bitr3i
    @22
    @5
    @6
    @11
    @21
    @0
    @5
    wta
    w-bnj17
    #
    @12
    vk
    wex
    @22
    @5
    wa
    @12
    @25
    @25
    @2
    vk
    cv
    #
    csuc
    wceq
    #
    wa
    #
    @12
    vk
    @25
    @27
    vk
    @25
    @21
    @0
    @5
    w3a
    #
    wta
    wa
    vk
    @21
    @0
    @5
    wta
    df-bnj17
    @29
    wta
    vk
    wta
    @26
    @2
    cep
    wbr
    #
    wth
    vj
    @26
    wsbc
    #
    wi
    #
    vk
    @4
    bnj594.17
    bnj1095
    bnj1352
    hbxfrbi
    @21
    @0
    @5
    wta
    @27
    vk
    wex
    #
    @29
    @2
    com
    wcel
    #
    @21
    wa
    #
    @27
    vk
    com
    wrex
    @33
    @29
    @0
    @5
    wa
    #
    @21
    wa
    @35
    @21
    @0
    @5
    bnj170
    @36
    @34
    @21
    @5
    @0
    @4
    com
    wcel
    #
    @34
    cD
    vn
    bnj594.7
    bnj923
    @2
    @4
    elnn
    sylan2
    #
    anim1i
    sylbi
    vk
    @2
    nnsuc
    @27
    vk
    com
    rexex
    3syl
    bnj721
    bnj596
    @28
    @0
    @5
    @27
    wta
    w-bnj17
    #
    @12
    @28
    @0
    @5
    wta
    w3a
    #
    @27
    wa
    @39
    @25
    @40
    @27
    @21
    @0
    @5
    wta
    bnj667
    anim1i
    @0
    @5
    @27
    wta
    bnj258
    sylibr
    @39
    @6
    @11
    @39
    @6
    wa
    #
    vy
    @26
    @7
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
    vy
    @26
    @9
    cfv
    #
    @43
    ciun
    #
    @8
    @10
    @41
    @31
    @5
    wch
    bnjwchm
    w-bnj17
    #
    @42
    @45
    wceq
    #
    @44
    @46
    wceq
    @41
    @31
    @6
    wa
    @47
    @39
    @31
    @6
    @39
    @0
    @5
    @27
    w3a
    #
    wta
    wa
    #
    @31
    @0
    @5
    @27
    wta
    df-bnj17
    @50
    @30
    @31
    @49
    @30
    wta
    @27
    @0
    @30
    @5
    vk
    vj
    bnj219
    3ad2ant3
    adantr
    @49
    vk
    vn
    wel
    #
    wta
    @32
    @27
    @0
    @5
    vk
    vj
    wel
    #
    @51
    @2
    @26
    vk
    vex
    bnj216
    #
    @0
    @5
    @52
    w3a
    #
    @5
    @52
    @0
    wa
    #
    wa
    #
    @51
    @52
    @0
    @5
    w3a
    @55
    @5
    wa
    @54
    @56
    @52
    @0
    @5
    df-3an
    @52
    @0
    @5
    3anrot
    @55
    @5
    ancom
    3bitr3i
    @5
    @55
    @51
    @5
    @37
    @4
    word
    @55
    @51
    wi
    @37
    @4
    com
    c0
    csn
    #
    cdif
    cD
    @4
    com
    @57
    eldifi
    bnj594.7
    eleq2s
    @4
    nnord
    @26
    @2
    @4
    ordtr1
    3syl
    imp
    sylbi
    syl3an3
    wta
    @32
    vk
    @4
    wral
    @51
    @32
    wi
    bnj594.17
    @32
    vk
    @4
    rsp
    sylbi
    mpan9
    mpd
    sylbi
    anim1i
    @31
    @5
    wch
    bnjwchm
    bnj252
    sylibr
    @47
    @6
    @31
    wa
    @48
    @31
    @5
    wch
    bnjwchm
    bnj446
    @31
    @6
    @6
    @48
    wi
    @48
    bnj594.16
    @6
    @48
    pm3.35
    sylan2b
    sylbi
    vy
    @42
    @45
    @43
    iuneq1
    3syl
    @41
    @49
    wps
    bnjwpsm
    wa
    #
    wa
    #
    @49
    wps
    wa
    @8
    @44
    wceq
    #
    @39
    @49
    @6
    @58
    @0
    @5
    @27
    wta
    bnj658
    @5
    wch
    bnjwchm
    wps
    bnjwpsm
    wch
    @19
    wph
    wps
    bnj594.3
    simp3bi
    bnjwchm
    @20
    bnjwphm
    bnjwpsm
    bnj594.11
    simp3bi
    bnj240
    anim12i
    #
    @58
    wps
    @49
    wps
    bnjwpsm
    simpl
    anim2i
    @49
    wps
    @27
    wps
    wa
    #
    @60
    @49
    @27
    wps
    @0
    @5
    @27
    simp3
    #
    anim1i
    @49
    @62
    wa
    @0
    @60
    @0
    @5
    @27
    @62
    simpl1
    @49
    @26
    com
    wcel
    #
    @62
    @0
    @60
    wi
    @49
    @27
    @36
    wa
    #
    @64
    @49
    @36
    @27
    wa
    @65
    @0
    @5
    @27
    df-3an
    @36
    @27
    ancom
    bitri
    @27
    @52
    @34
    @64
    @36
    @53
    @38
    @26
    @2
    elnn
    syl2an
    sylbi
    #
    wps
    vy
    cA
    @2
    cR
    vf
    vk
    vn
    wps
    vy
    cA
    cR
    vf
    vi
    vk
    vn
    bnj594.2
    bnj589
    bnj590
    mpan9
    mpd
    syldan
    3syl
    @41
    @59
    @49
    bnjwpsm
    wa
    @10
    @46
    wceq
    #
    @61
    @58
    bnjwpsm
    @49
    wps
    bnjwpsm
    simpr
    anim2i
    @49
    bnjwpsm
    @27
    bnjwpsm
    wa
    #
    @67
    @49
    @27
    bnjwpsm
    @63
    anim1i
    @49
    @68
    wa
    @0
    @67
    @0
    @5
    @27
    @68
    simpl1
    @49
    @64
    @68
    @0
    @67
    wi
    @66
    bnjwpsm
    vy
    cA
    @2
    cR
    vg
    vk
    vn
    bnjwpsm
    vy
    cA
    cR
    vg
    vi
    vk
    vn
    bnj594.10
    bnj589
    bnj590
    mpan9
    mpd
    syldan
    3syl
    3eqtr4d
    ex
    syl
    bnj593
    @21
    @0
    @5
    wta
    bnj258
    @12
    vk
    19.9v
    3imtr3i
    expimpd
    syl5bir
    bnj594.15
    sylibr
    3expib
    pm2.61ine
end
