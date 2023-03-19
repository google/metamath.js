include "c-bnj18.mm"
include "wcel.mm"
include "wex.mm"
include "wel.mm"
include "cv.mm"
include "cfv.mm"
include "w3a.mm"
include "bnj981.mm"
include "wss.mm"
include "simp1.mm"
include "simp2.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "nfv.mm"
include "cep.mm"
include "wbr.mm"
include "wsbc.mm"
include "nfra1.mm"
include "nfxfr.mm"
include "nf3an.mm"
include "nfim.mm"
include "nf5ri.mm"
include "c0.mm"
include "wne.mm"
include "csuc.mm"
include "wceq.mm"
include "bnj1098.mm"
include "simpl.mm"
include "simpr1.mm"
include "wfn.mm"
include "bnj1232.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "3jca.mm"
include "bnj1101.mm"
include "ancl.mm"
include "bnj101.mm"
include "df-3an.mm"
include "imbi2i.mm"
include "exbii.mm"
include "mpbir.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "bnj213.mm"
include "bnj226.mm"
include "simp21.mm"
include "com.mm"
include "simp3r.mm"
include "w-bnj17.mm"
include "biid.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "sbcg.mm"
include "ax-mp.mm"
include "bitr2i.mm"
include "bnj1039.mm"
include "bitr4i.mm"
include "bnj887.mm"
include "bnj1040.mm"
include "3bitr4i.mm"
include "bnj1254.mm"
include "sylbi.mm"
include "3ad2ant2.mm"
include "simp3l.mm"
include "bnj923.mm"
include "elnn.mm"
include "sylan2.mm"
include "syl2anc.mm"
include "bnj589.mm"
include "rsp.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "syl5ibr.mm"
include "syl3c.mm"
include "mpd.mm"
include "bnj1262.mm"
include "bnj1023.mm"
include "bnj1247.mm"
include "biimpi.mm"
include "sylan9eq.mm"
include "bnj1109.mm"
include "bnj1131.mm"
include "3expia.mm"
include "sylibr.mm"
include "bnj1133.mm"
include "ralbii.mm"
include "sylib.mm"
include "syl.mm"
include "simp3.mm"
include "sseldd.mm"
include "2eximi.mm"
include "bnj593.mm"
include "19.9v.mm"
include "3bitri.mm"

theorem bnj1128
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cX: class X
  let cY: class Y
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  let bnjwthm: wff th'
  assume bnj1128.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj1128.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1128.3: |- D = ( _om \ { (/) } )
  assume bnj1128.4: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj1128.5: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1128.6: |- ( th <-> ( ch -> ( f ` i ) C_ A ) )
  assume bnj1128.7: |- ( ta <-> A. j e. n ( j _E i -> [. j / i ]. th ) )
  assume bnj1128.8: |- ( ph' <-> [. j / i ]. ph )
  assume bnj1128.9: |- ( ps' <-> [. j / i ]. ps )
  assume bnj1128.10: |- ( ch' <-> [. j / i ]. ch )
  assume bnj1128.11: |- ( th' <-> [. j / i ]. th )

  disjoint A f
  disjoint A i
  disjoint A j
  disjoint A n
  disjoint A y
  disjoint f i
  disjoint f j
  disjoint f n
  disjoint f y
  disjoint i j
  disjoint i n
  disjoint i y
  disjoint j n
  disjoint j y
  disjoint n y
  disjoint D i
  disjoint D j
  disjoint D y
  disjoint R f
  disjoint R i
  disjoint R j
  disjoint R n
  disjoint R y
  disjoint X f
  disjoint X i
  disjoint X n
  disjoint X y
  disjoint Y f
  disjoint Y i
  disjoint Y n
  disjoint Y y
  disjoint ch j
  disjoint i ph
  disjoint ph y
  disjoint j th
  assert |- ( Y e. _trCl ( X , A , R ) -> Y e. A )

  proof
    cY
    cA
    cR
    cX
    c-bnj18
    wcel
    #
    cY
    cA
    wcel
    #
    vi
    wex
    #
    vn
    wex
    #
    vf
    wex
    #
    @1
    @0
    wch
    vi
    vn
    wel
    #
    cY
    vi
    cv
    #
    vf
    cv
    #
    cfv
    #
    wcel
    #
    w3a
    #
    vi
    wex
    vn
    wex
    @3
    vf
    wph
    wps
    wch
    vy
    cA
    cB
    cD
    cR
    vf
    vi
    vn
    cX
    cY
    bnj1128.1
    bnj1128.2
    bnj1128.3
    bnj1128.4
    bnj1128.5
    bnj981
    @10
    @1
    vn
    vi
    @10
    @8
    cA
    cY
    @10
    wch
    @5
    wch
    @8
    cA
    wss
    #
    wch
    @5
    @9
    simp1
    #
    wch
    @5
    @9
    simp2
    @12
    wch
    wch
    @11
    wi
    #
    vi
    vn
    cv
    #
    wral
    #
    @5
    @13
    wi
    wch
    wth
    vi
    @14
    wral
    @15
    wph
    wps
    wch
    wth
    wta
    cD
    vf
    vi
    vj
    vn
    bnj1128.3
    bnj1128.5
    bnj1128.7
    @5
    wta
    wa
    @13
    wth
    @5
    wta
    wch
    @11
    @5
    wta
    wch
    w3a
    #
    @11
    wi
    #
    vj
    @17
    vj
    @16
    @11
    vj
    @5
    wta
    wch
    vj
    @5
    vj
    nfv
    wta
    vj
    cv
    #
    @6
    cep
    wbr
    wth
    vi
    @18
    wsbc
    wi
    #
    vj
    @14
    wral
    vj
    bnj1128.7
    @19
    vj
    @14
    nfra1
    nfxfr
    wch
    vj
    nfv
    nf3an
    @11
    vj
    nfv
    nfim
    nf5ri
    @16
    @11
    vj
    @6
    c0
    @6
    c0
    wne
    #
    @16
    wa
    #
    @20
    @16
    vj
    vn
    wel
    #
    @6
    @18
    csuc
    #
    wceq
    #
    wa
    #
    w3a
    #
    @11
    vj
    @21
    @26
    wi
    #
    vj
    wex
    @21
    @21
    @25
    wa
    #
    wi
    #
    vj
    wex
    @21
    @25
    wi
    @29
    vj
    @20
    @5
    @14
    cD
    wcel
    #
    w3a
    @25
    @21
    vj
    cD
    vi
    vj
    vn
    bnj1128.3
    bnj1098
    @21
    @20
    @5
    @30
    @20
    @16
    simpl
    @20
    @5
    wta
    wch
    simpr1
    @16
    @30
    @20
    wch
    @5
    @30
    wta
    wch
    @30
    @7
    @14
    wfn
    #
    wph
    wps
    bnj1128.5
    bnj1232
    3ad2ant3
    #
    adantl
    3jca
    bnj1101
    @21
    @25
    ancl
    bnj101
    @27
    @29
    vj
    @26
    @28
    @21
    @20
    @16
    @25
    df-3an
    imbi2i
    exbii
    mpbir
    @26
    vy
    @18
    @7
    cfv
    #
    cA
    cR
    vy
    cv
    #
    c-bnj14
    #
    ciun
    #
    cA
    @8
    vy
    @33
    @35
    cA
    cA
    cR
    @34
    bnj213
    bnj226
    @26
    @5
    @8
    @36
    wceq
    #
    @20
    @5
    wta
    wch
    @25
    simp21
    @26
    @24
    bnjwpsm
    @18
    com
    wcel
    #
    @5
    @37
    wi
    #
    @20
    @16
    @22
    @24
    simp3r
    @16
    @20
    bnjwpsm
    @25
    wch
    @5
    bnjwpsm
    wta
    wch
    bnjwchm
    bnjwpsm
    @30
    @31
    wph
    wps
    w-bnj17
    @30
    @31
    bnjwphm
    bnjwpsm
    w-bnj17
    wch
    bnjwchm
    @30
    @31
    wph
    wps
    @30
    @31
    bnjwphm
    bnjwpsm
    @30
    biid
    @31
    biid
    bnjwphm
    wph
    vi
    @18
    wsbc
    #
    wph
    bnj1128.8
    @18
    cvv
    wcel
    @40
    wph
    wb
    vj
    vex
    wph
    vi
    @18
    cvv
    sbcg
    ax-mp
    bitr2i
    wps
    @6
    csuc
    #
    @14
    wcel
    @41
    @7
    cfv
    vy
    @8
    @35
    ciun
    wceq
    wi
    vi
    com
    wral
    bnjwpsm
    bnj1128.2
    wps
    vy
    cA
    cR
    vf
    vi
    vj
    vn
    bnjwpsm
    bnj1128.2
    bnj1128.9
    bnj1039
    #
    bitr4i
    bnj887
    bnj1128.5
    wph
    wps
    wch
    cD
    vf
    vi
    vj
    vn
    bnjwphm
    bnjwpsm
    bnjwchm
    bnj1128.8
    bnj1128.9
    bnj1128.5
    bnj1128.10
    bnj1040
    #
    3bitr4i
    bnjwchm
    @30
    @31
    bnjwphm
    bnjwpsm
    @43
    bnj1254
    sylbi
    3ad2ant3
    3ad2ant2
    @26
    @22
    @30
    @38
    @20
    @16
    @22
    @24
    simp3l
    @16
    @20
    @30
    @25
    @32
    3ad2ant2
    @30
    @22
    @14
    com
    wcel
    @38
    cD
    vn
    bnj1128.3
    bnj923
    @18
    @14
    elnn
    sylan2
    syl2anc
    bnjwpsm
    @38
    @39
    wi
    @24
    @38
    @23
    @14
    wcel
    #
    @23
    @7
    cfv
    #
    @36
    wceq
    #
    wi
    #
    wi
    #
    bnjwpsm
    @47
    vj
    com
    wral
    @48
    bnjwpsm
    vy
    cA
    cR
    vf
    vi
    vj
    vn
    @42
    bnj589
    @47
    vj
    com
    rsp
    sylbi
    @24
    @39
    @47
    @38
    @24
    @5
    @44
    @37
    @46
    @6
    @23
    @14
    eleq1
    @24
    @8
    @45
    @36
    @6
    @23
    @7
    fveq2
    eqeq1d
    imbi12d
    imbi2d
    syl5ibr
    syl3c
    mpd
    bnj1262
    bnj1023
    @16
    @6
    c0
    wceq
    #
    wph
    @11
    wch
    @5
    wph
    wta
    wch
    @30
    @31
    wph
    wps
    bnj1128.5
    bnj1247
    3ad2ant3
    @49
    wph
    wa
    cA
    cR
    cX
    c-bnj14
    #
    cA
    @8
    cA
    cR
    cX
    bnj213
    @49
    wph
    @8
    c0
    @7
    cfv
    #
    @50
    @6
    c0
    @7
    fveq2
    wph
    @51
    @50
    wceq
    bnj1128.1
    biimpi
    sylan9eq
    bnj1262
    sylan2
    bnj1109
    bnj1131
    3expia
    bnj1128.6
    sylibr
    bnj1133
    wth
    @13
    vi
    @14
    bnj1128.6
    ralbii
    sylib
    @13
    vi
    @14
    rsp
    syl
    syl3c
    wch
    @5
    @9
    simp3
    sseldd
    2eximi
    bnj593
    @4
    @3
    @2
    @1
    @3
    vf
    19.9v
    @2
    vn
    19.9v
    @1
    vi
    19.9v
    3bitri
    sylib
end
