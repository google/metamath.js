include "c-bnj18.mm"
include "cv.mm"
include "cdm.mm"
include "cfv.mm"
include "ciun.mm"
include "bnj882.mm"
include "wss.mm"
include "ss2iun.mm"
include "wcel.mm"
include "wral.mm"
include "wex.mm"
include "bnj1083.mm"
include "wfn.mm"
include "csuc.mm"
include "c-bnj14.mm"
include "wceq.mm"
include "wi.mm"
include "com.mm"
include "bnj1095.mm"
include "bnj1096.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "bnj1098.mm"
include "bnj1232.mm"
include "3anim3i.mm"
include "bnj1101.mm"
include "ancl.mm"
include "bnj101.mm"
include "imbi2i.mm"
include "exbii.mm"
include "mpbir.mm"
include "bnj213.mm"
include "bnj226.mm"
include "simpr.mm"
include "simplbiim.mm"
include "simp2.mm"
include "3ad2ant3.mm"
include "bnj923.mm"
include "elnn.mm"
include "sylan2.mm"
include "syl2anc.mm"
include "bnj832.mm"
include "vex.mm"
include "bnj216.mm"
include "sylan.mm"
include "eqeltrrd.mm"
include "w-bnj17.mm"
include "bnj589.mm"
include "biimpi.mm"
include "bnj708.mm"
include "rsp.mm"
include "syl.mm"
include "sylbi.mm"
include "mp2d.mm"
include "wb.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "mpbird.mm"
include "bnj1262.mm"
include "bnj1023.mm"
include "3anass.mm"
include "imbi1i.mm"
include "mpbi.mm"
include "bnj771.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "biimpar.mm"
include "syl2an.mm"
include "adantrl.mm"
include "bnj1109.mm"
include "19.9v.mm"
include "expcom.mm"
include "fndm.mm"
include "bnj770.mm"
include "eleq2.mm"
include "imbi1d.mm"
include "hbralrimi.mm"
include "exlimiv.mm"
include "bnj1143.mm"
include "syl6ss.mm"
include "mprg.mm"
include "wrex.mm"
include "bnj1317.mm"
include "bnj1146.mm"
include "sstri.mm"
include "eqsstri.mm"

theorem bnj1145
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
  let vw: setvar w
  assume bnj1145.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj1145.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1145.3: |- D = ( _om \ { (/) } )
  assume bnj1145.4: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj1145.5: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1145.6: |- ( th <-> ( ( i =/= (/) /\ i e. n /\ ch ) /\ ( j e. n /\ i = suc j ) ) )

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
  disjoint R f
  disjoint R i
  disjoint R j
  disjoint R n
  disjoint R y
  disjoint X f
  disjoint X i
  disjoint X n
  disjoint X y
  disjoint ch j
  disjoint i ph
  disjoint A w
  disjoint f w
  disjoint B w
  assert |- _trCl ( X , A , R ) C_ A

  proof
    cA
    cR
    cX
    c-bnj18
    vf
    cB
    vi
    vf
    cv
    #
    cdm
    #
    vi
    cv
    #
    @0
    cfv
    #
    ciun
    #
    ciun
    #
    cA
    wph
    wps
    vy
    cA
    cB
    cD
    cR
    vf
    vi
    vn
    cX
    bnj1145.1
    bnj1145.2
    bnj1145.3
    bnj1145.4
    bnj882
    @5
    vf
    cB
    cA
    ciun
    #
    cA
    @4
    cA
    wss
    #
    @5
    @6
    wss
    vf
    cB
    vf
    cB
    @4
    cA
    ss2iun
    @0
    cB
    wcel
    #
    @3
    cA
    wss
    #
    vi
    @1
    wral
    #
    @7
    @8
    wch
    vn
    wex
    @10
    wph
    wps
    wch
    cD
    vf
    vn
    cB
    bnj1145.5
    bnj1145.4
    bnj1083
    wch
    @10
    vn
    wch
    @9
    vi
    @1
    wps
    wch
    vn
    cv
    #
    cD
    wcel
    #
    @0
    @11
    wfn
    #
    wph
    vi
    wps
    @2
    csuc
    #
    @11
    wcel
    @14
    @0
    cfv
    vy
    @3
    cA
    cR
    vy
    cv
    #
    c-bnj14
    #
    ciun
    wceq
    wi
    vi
    com
    bnj1145.2
    bnj1095
    bnj1145.5
    bnj1096
    wch
    @2
    @1
    wcel
    #
    @9
    wi
    #
    @2
    @11
    wcel
    #
    @9
    wi
    #
    @19
    wch
    @9
    @19
    wch
    wa
    #
    @9
    wi
    #
    vj
    wex
    @22
    @21
    @9
    vj
    @2
    c0
    @2
    c0
    wne
    #
    @19
    wch
    w3a
    #
    @9
    wi
    #
    vj
    wex
    @23
    @21
    wa
    #
    @9
    wi
    #
    vj
    wex
    @24
    wth
    @9
    vj
    @24
    wth
    wi
    #
    vj
    wex
    @24
    @24
    vj
    cv
    #
    @11
    wcel
    #
    @2
    @29
    csuc
    #
    wceq
    #
    wa
    #
    wa
    #
    wi
    #
    vj
    wex
    @24
    @33
    wi
    @35
    vj
    @23
    @19
    @12
    w3a
    @33
    @24
    vj
    cD
    vi
    vj
    vn
    bnj1145.3
    bnj1098
    wch
    @12
    @23
    @19
    wch
    @12
    @13
    wph
    wps
    bnj1145.5
    bnj1232
    #
    3anim3i
    bnj1101
    @24
    @33
    ancl
    bnj101
    @28
    @35
    vj
    wth
    @34
    @24
    bnj1145.6
    imbi2i
    exbii
    mpbir
    wth
    vy
    @29
    @0
    cfv
    #
    @16
    ciun
    #
    cA
    @3
    vy
    @37
    @16
    cA
    cA
    cR
    @15
    bnj213
    bnj226
    wth
    @3
    @38
    wceq
    #
    @31
    @0
    cfv
    #
    @38
    wceq
    #
    wth
    @29
    com
    wcel
    #
    @31
    @11
    wcel
    #
    @41
    wth
    @32
    @2
    com
    wcel
    #
    @42
    wth
    @24
    @33
    @32
    bnj1145.6
    @30
    @32
    simpr
    simplbiim
    #
    @24
    @33
    @44
    wth
    bnj1145.6
    @24
    @19
    @12
    @44
    @23
    @19
    wch
    simp2
    #
    wch
    @23
    @12
    @19
    @36
    3ad2ant3
    @12
    @19
    @11
    com
    wcel
    @44
    cD
    vn
    bnj1145.3
    bnj923
    @2
    @11
    elnn
    sylan2
    syl2anc
    bnj832
    @32
    @29
    @2
    wcel
    @44
    @42
    @2
    @29
    vj
    vex
    bnj216
    @29
    @2
    elnn
    sylan
    syl2anc
    wth
    @2
    @31
    @11
    @45
    @24
    @33
    @19
    wth
    bnj1145.6
    @46
    bnj832
    eqeltrrd
    @24
    @33
    @42
    @43
    @41
    wi
    #
    wi
    #
    wth
    bnj1145.6
    wch
    @23
    @48
    @19
    wch
    @12
    @13
    wph
    wps
    w-bnj17
    #
    @48
    bnj1145.5
    @49
    @47
    vj
    com
    wral
    #
    @48
    @12
    @13
    wph
    wps
    @50
    wps
    @50
    wps
    vy
    cA
    cR
    vf
    vi
    vj
    vn
    bnj1145.2
    bnj589
    biimpi
    bnj708
    @47
    vj
    com
    rsp
    syl
    sylbi
    3ad2ant3
    bnj832
    mp2d
    wth
    @32
    @39
    @41
    wb
    @45
    @32
    @3
    @40
    @38
    @2
    @31
    @0
    fveq2
    eqeq1d
    syl
    mpbird
    bnj1262
    bnj1023
    @25
    @27
    vj
    @24
    @26
    @9
    @23
    @19
    wch
    3anass
    imbi1i
    exbii
    mpbi
    @2
    c0
    wceq
    #
    wch
    @9
    @19
    wch
    @51
    c0
    @0
    cfv
    #
    cA
    cR
    cX
    c-bnj14
    #
    wceq
    #
    @9
    @12
    @13
    wph
    wps
    @54
    wch
    bnj1145.5
    wph
    @54
    bnj1145.1
    biimpi
    bnj771
    @51
    @3
    @52
    wceq
    #
    @52
    cA
    wss
    #
    @9
    @54
    @2
    c0
    @0
    fveq2
    @54
    @56
    @53
    cA
    wss
    cA
    cR
    cX
    bnj213
    @52
    @53
    cA
    sseq1
    mpbiri
    @55
    @9
    @56
    @3
    @52
    cA
    sseq1
    biimpar
    syl2an
    sylan2
    adantrl
    bnj1109
    @22
    vj
    19.9v
    mpbi
    expcom
    wch
    @1
    @11
    wceq
    #
    @18
    @20
    wb
    @12
    @13
    wph
    wps
    @57
    wch
    bnj1145.5
    @11
    @0
    fndm
    bnj770
    @57
    @17
    @19
    @9
    @1
    @11
    @2
    eleq2
    imbi1d
    syl
    mpbird
    hbralrimi
    exlimiv
    sylbi
    @10
    @4
    vi
    @1
    cA
    ciun
    cA
    vi
    @1
    @3
    cA
    ss2iun
    vi
    @1
    cA
    bnj1143
    syl6ss
    syl
    mprg
    vf
    vw
    cB
    cA
    @13
    wph
    wps
    w3a
    vn
    cD
    wrex
    vf
    vw
    cB
    bnj1145.4
    bnj1317
    bnj1146
    sstri
    eqsstri
end
