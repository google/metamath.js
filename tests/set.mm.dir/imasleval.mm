include "wcel.mm"
include "cfv.mm"
include "wbr.mm"
include "wb.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "breq1.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "breq2d.mm"
include "breq2.mm"
include "ccom.mm"
include "ccnv.mm"
include "wrex.mm"
include "cdm.mm"
include "wfn.mm"
include "wfo.mm"
include "fofn.mm"
include "syl.mm"
include "adantr.mm"
include "fndm.mm"
include "rexeqdv.mm"
include "fnbrfvb.mm"
include "sylan.mm"
include "anbi1d.mm"
include "wex.mm"
include "ancom.mm"
include "vex.mm"
include "fvex.mm"
include "breldm.mm"
include "pm4.71ri.mm"
include "bitri.mm"
include "exbii.mm"
include "brco.mm"
include "df-rex.mm"
include "3bitr4i.mm"
include "ad2antrr.mm"
include "3expa.mm"
include "an32s.mm"
include "anassrs.mm"
include "impl.mm"
include "pm5.32da.mm"
include "bitr3d.mm"
include "rexbidva.mm"
include "r19.41v.mm"
include "syl6bb.mm"
include "simprr.mm"
include "eqid.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "biantrurd.mm"
include "3bitr4d.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "brcnv.mm"
include "anbi1i.mm"
include "3bitr4ri.mm"
include "3bitr3g.mm"
include "imasle.mm"
include "breqd.mm"
include "simprl.mm"
include "expcom.mm"
include "vtocl2ga.mm"
include "com12.mm"
include "3impib.mm"

theorem imasleval
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cF: class F
  let c.le: class .<_
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume imasless.u: |- ( ph -> U = ( F "s R ) )
  assume imasless.v: |- ( ph -> V = ( Base ` R ) )
  assume imasless.f: |- ( ph -> F : V -onto-> B )
  assume imasless.r: |- ( ph -> R e. Z )
  assume imasless.l: |- .<_ = ( le ` U )
  assume imasleval.n: |- N = ( le ` R )
  assume imasleval.e: |- ( ( ph /\ ( a e. V /\ b e. V ) /\ ( c e. V /\ d e. V ) ) -> ( ( ( F ` a ) = ( F ` c ) /\ ( F ` b ) = ( F ` d ) ) -> ( a N b <-> c N d ) ) )

  disjoint c d
  disjoint .<_ c
  disjoint .<_ d
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint F a
  disjoint b c
  disjoint b d
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint N d
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V d
  disjoint Y d
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint X c
  disjoint X d
  assert |- ( ( ph /\ X e. V /\ Y e. V ) -> ( ( F ` X ) .<_ ( F ` Y ) <-> X N Y ) )

  proof
    wph
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    c.le
    wbr
    #
    cX
    cY
    cN
    wbr
    #
    wb
    #
    @0
    @1
    wa
    wph
    @6
    wph
    vc
    cv
    #
    cF
    cfv
    #
    vd
    cv
    #
    cF
    cfv
    #
    c.le
    wbr
    #
    @7
    @9
    cN
    wbr
    #
    wb
    #
    wi
    wph
    @2
    @10
    c.le
    wbr
    #
    cX
    @9
    cN
    wbr
    #
    wb
    #
    wi
    wph
    @6
    wi
    vc
    vd
    cX
    cY
    cV
    cV
    @7
    cX
    wceq
    #
    @13
    @16
    wph
    @17
    @11
    @14
    @12
    @15
    @17
    @8
    @2
    @10
    c.le
    @7
    cX
    cF
    fveq2
    breq1d
    @7
    cX
    @9
    cN
    breq1
    bibi12d
    imbi2d
    @9
    cY
    wceq
    #
    @16
    @6
    wph
    @18
    @14
    @4
    @15
    @5
    @18
    @10
    @3
    @2
    c.le
    @9
    cY
    cF
    fveq2
    breq2d
    @9
    cY
    cX
    cN
    breq2
    bibi12d
    imbi2d
    wph
    @7
    cV
    wcel
    #
    @9
    cV
    wcel
    #
    wa
    #
    @13
    wph
    @21
    wa
    #
    @8
    @10
    cF
    cN
    ccom
    #
    cF
    ccnv
    #
    ccom
    #
    wbr
    #
    va
    cv
    #
    cF
    cfv
    #
    @8
    wceq
    #
    va
    cV
    wrex
    #
    @12
    wa
    #
    @11
    @12
    @22
    @27
    @8
    cF
    wbr
    #
    @27
    @10
    @23
    wbr
    #
    wa
    #
    va
    cF
    cdm
    #
    wrex
    #
    @29
    @12
    wa
    #
    va
    cV
    wrex
    #
    @26
    @31
    @22
    @36
    @34
    va
    cV
    wrex
    @38
    @22
    @34
    va
    @35
    cV
    @22
    cF
    cV
    wfn
    #
    @35
    cV
    wceq
    wph
    @39
    @21
    wph
    cV
    cB
    cF
    wfo
    @39
    imasless.f
    cV
    cB
    cF
    fofn
    syl
    adantr
    #
    cV
    cF
    fndm
    syl
    #
    rexeqdv
    @22
    @34
    @37
    va
    cV
    @22
    @27
    cV
    wcel
    #
    wa
    #
    @29
    @33
    wa
    @34
    @37
    @43
    @29
    @32
    @33
    @22
    @39
    @42
    @29
    @32
    wb
    @40
    cV
    @27
    @8
    cF
    fnbrfvb
    sylan
    anbi1d
    @43
    @29
    @33
    @12
    @33
    vb
    cv
    #
    @10
    cF
    wbr
    #
    @27
    @44
    cN
    wbr
    #
    wa
    #
    vb
    @35
    wrex
    #
    @43
    @29
    wa
    #
    @12
    @46
    @45
    wa
    #
    vb
    wex
    @44
    @35
    wcel
    #
    @47
    wa
    #
    vb
    wex
    @33
    @48
    @50
    @52
    vb
    @50
    @47
    @52
    @46
    @45
    ancom
    @47
    @51
    @45
    @51
    @46
    @44
    @10
    cF
    vb
    vex
    @9
    cF
    fvex
    #
    breldm
    adantr
    pm4.71ri
    bitri
    exbii
    vb
    @27
    @10
    cF
    cN
    va
    vex
    #
    @53
    brco
    @47
    vb
    @35
    df-rex
    3bitr4i
    @49
    @47
    vb
    cV
    wrex
    #
    @44
    cF
    cfv
    #
    @10
    wceq
    #
    vb
    cV
    wrex
    #
    @12
    wa
    #
    @48
    @12
    @49
    @55
    @57
    @12
    wa
    #
    vb
    cV
    wrex
    @59
    @49
    @47
    @60
    vb
    cV
    @49
    @44
    cV
    wcel
    #
    wa
    #
    @57
    @46
    wa
    #
    @47
    @60
    @62
    @57
    @45
    @46
    @49
    @39
    @61
    @57
    @45
    wb
    @22
    @39
    @42
    @29
    @40
    ad2antrr
    cV
    @44
    @10
    cF
    fnbrfvb
    sylan
    anbi1d
    @43
    @61
    @29
    @63
    @60
    wb
    @43
    @61
    wa
    #
    @29
    wa
    @57
    @46
    @12
    @64
    @29
    @57
    @46
    @12
    wb
    #
    @22
    @42
    @61
    @29
    @57
    wa
    @65
    wi
    #
    wph
    @42
    @61
    wa
    #
    @21
    @66
    wph
    @67
    @21
    @66
    imasleval.e
    3expa
    an32s
    anassrs
    impl
    pm5.32da
    an32s
    bitr3d
    rexbidva
    @57
    @12
    vb
    cV
    r19.41v
    syl6bb
    @22
    @48
    @55
    wb
    @42
    @29
    @22
    @47
    vb
    @35
    cV
    @41
    rexeqdv
    ad2antrr
    @22
    @12
    @59
    wb
    @42
    @29
    @22
    @58
    @12
    @22
    @20
    @10
    @10
    wceq
    #
    @58
    wph
    @19
    @20
    simprr
    @10
    eqid
    @57
    @68
    vb
    @9
    cV
    @44
    @9
    wceq
    @56
    @10
    @10
    @44
    @9
    cF
    fveq2
    eqeq1d
    rspcev
    sylancl
    biantrurd
    ad2antrr
    3bitr4d
    syl5bb
    pm5.32da
    bitr3d
    rexbidva
    bitrd
    @8
    @27
    @24
    wbr
    #
    @33
    wa
    #
    va
    wex
    @27
    @35
    wcel
    #
    @34
    wa
    #
    va
    wex
    @26
    @36
    @70
    @72
    va
    @70
    @34
    @72
    @69
    @32
    @33
    @8
    @27
    cF
    @7
    cF
    fvex
    #
    @54
    brcnv
    anbi1i
    @34
    @71
    @32
    @71
    @33
    @27
    @8
    cF
    @54
    @73
    breldm
    adantr
    pm4.71ri
    bitri
    exbii
    va
    @8
    @10
    @23
    @24
    @73
    @53
    brco
    @34
    va
    @35
    df-rex
    3bitr4ri
    @29
    @12
    va
    cV
    r19.41v
    3bitr3g
    @22
    c.le
    @25
    @8
    @10
    wph
    c.le
    @25
    wceq
    @21
    wph
    cB
    cR
    cU
    cF
    c.le
    cN
    cV
    cZ
    imasless.u
    imasless.v
    imasless.f
    imasless.r
    imasleval.n
    imasless.l
    imasle
    adantr
    breqd
    @22
    @30
    @12
    @22
    @19
    @8
    @8
    wceq
    #
    @30
    wph
    @19
    @20
    simprl
    @8
    eqid
    @29
    @74
    va
    @7
    cV
    @27
    @7
    wceq
    @28
    @8
    @8
    @27
    @7
    cF
    fveq2
    eqeq1d
    rspcev
    sylancl
    biantrurd
    3bitr4d
    expcom
    vtocl2ga
    com12
    3impib
end
