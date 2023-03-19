include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "crab.mm"
include "cdioph.mm"
include "cfv.mm"
include "wa.mm"
include "wrex.mm"
include "cv.mm"
include "cres.mm"
include "wceq.mm"
include "cab.mm"
include "wsbc.mm"
include "df-rab.mm"
include "dfsbcq.mm"
include "cbvrexv.mm"
include "anbi2i.mm"
include "r19.42v.mm"
include "bitr4i.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "simpll.mm"
include "simpr.mm"
include "simplr.mm"
include "mapfzcons.mm"
include "syl3anc.mm"
include "adantrr.mm"
include "mapfzcons2.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "mapfzcons1.mm"
include "adantl.mm"
include "sbceq1d.mm"
include "sbceqbid.mm"
include "biimpd.mm"
include "impr.mm"
include "fveq1.mm"
include "reseq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ex.mm"
include "rexlimdva.mm"
include "wf.mm"
include "elmapi.mm"
include "cn.mm"
include "caddc.mm"
include "nn0p1nn.mm"
include "syl5eqel.mm"
include "elfz1end.mm"
include "sylib.mm"
include "ffvelrn.mm"
include "syl2anr.mm"
include "adantr.mm"
include "simprr.mm"
include "mapfzcons1cl.mm"
include "ad2antlr.mm"
include "eqeltrd.mm"
include "simprl.mm"
include "wb.mm"
include "sbcbidv.mm"
include "ad2antll.mm"
include "mpbird.mm"
include "anbi2d.mm"
include "impbid.mm"
include "syl5bb.mm"
include "abbidv.mm"
include "syl5eq.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "nfsbc.mm"
include "nfrex.mm"
include "weq.mm"
include "sbceq1a.mm"
include "rexbidv.mm"
include "cbvrex.mm"
include "syl6bb.mm"
include "cbvrab.mm"
include "rexrab.mm"
include "abbii.mm"
include "3eqtr4g.mm"
include "fvex.mm"
include "vex.mm"
include "resex.mm"
include "sylan9bb.mm"
include "sbc2ie.mm"
include "rabbii.mm"
include "rexeqi.mm"
include "syl6eq.mm"
include "cuz.mm"
include "simpl.mm"
include "cz.mm"
include "nn0z.mm"
include "uzid.mm"
include "peano2uz.mm"
include "3syl.mm"
include "diophrex.mm"

theorem rexrabdioph
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume rexrabdioph.1: |- M = ( N + 1 )
  assume rexrabdioph.2: |- ( v = ( t ` M ) -> ( ps <-> ch ) )
  assume rexrabdioph.3: |- ( u = ( t |` ( 1 ... N ) ) -> ( ch <-> ph ) )

  disjoint N t
  disjoint N u
  disjoint N v
  disjoint t u
  disjoint t v
  disjoint u v
  disjoint M t
  disjoint M u
  disjoint M v
  disjoint ph u
  disjoint ph v
  disjoint ps t
  disjoint ch v
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint a t
  disjoint b t
  disjoint c t
  disjoint a u
  disjoint b u
  disjoint c u
  disjoint a v
  disjoint b v
  disjoint c v
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint M a
  disjoint M b
  disjoint M c
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint a ps
  disjoint b ps
  disjoint c ps
  disjoint a ch
  disjoint b ch
  disjoint c ch
  assert |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... M ) ) | ph } e. ( Dioph ` M ) ) -> { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 ps } e. ( Dioph ` N ) )

  proof
    cN
    cn0
    wcel
    #
    wph
    vt
    cn0
    c1
    cM
    cfz
    co
    #
    cmap
    co
    #
    crab
    #
    cM
    cdioph
    cfv
    wcel
    #
    wa
    #
    wps
    vv
    cn0
    wrex
    #
    vu
    cn0
    c1
    cN
    cfz
    co
    #
    cmap
    co
    #
    crab
    #
    va
    cv
    #
    vb
    cv
    #
    @7
    cres
    #
    wceq
    #
    vb
    @3
    wrex
    #
    va
    cab
    #
    cN
    cdioph
    cfv
    #
    @0
    @9
    @15
    wceq
    @4
    @0
    @9
    @13
    vb
    wps
    vu
    vt
    cv
    #
    @7
    cres
    #
    wsbc
    #
    vv
    cM
    @17
    cfv
    #
    wsbc
    #
    vt
    @2
    crab
    #
    wrex
    #
    va
    cab
    #
    @15
    @0
    wps
    vu
    @10
    wsbc
    #
    vv
    @11
    wsbc
    #
    vb
    cn0
    wrex
    #
    va
    @8
    crab
    #
    wps
    vu
    @12
    wsbc
    #
    vv
    cM
    @11
    cfv
    #
    wsbc
    #
    @13
    wa
    #
    vb
    @2
    wrex
    #
    va
    cab
    #
    @9
    @24
    @0
    @28
    @10
    @8
    wcel
    #
    @27
    wa
    #
    va
    cab
    @34
    @27
    va
    @8
    df-rab
    @0
    @36
    @33
    va
    @36
    @35
    @25
    vv
    vc
    cv
    #
    wsbc
    #
    wa
    #
    vc
    cn0
    wrex
    #
    @0
    @33
    @36
    @35
    @38
    vc
    cn0
    wrex
    #
    wa
    @40
    @27
    @41
    @35
    @26
    @38
    vb
    vc
    cn0
    @25
    vv
    @11
    @37
    dfsbcq
    cbvrexv
    anbi2i
    @35
    @38
    vc
    cn0
    r19.42v
    bitr4i
    @0
    @40
    @33
    @0
    @39
    @33
    vc
    cn0
    @0
    @37
    cn0
    wcel
    #
    wa
    #
    @39
    @33
    @43
    @39
    wa
    @10
    cM
    @37
    cop
    csn
    cun
    #
    @2
    wcel
    #
    wps
    vu
    @44
    @7
    cres
    #
    wsbc
    #
    vv
    cM
    @44
    cfv
    #
    wsbc
    #
    @10
    @46
    wceq
    #
    @33
    @43
    @35
    @45
    @38
    @43
    @35
    wa
    #
    @0
    @35
    @42
    @45
    @0
    @42
    @35
    simpll
    @43
    @35
    simpr
    #
    @0
    @42
    @35
    simplr
    #
    @10
    cn0
    @37
    cM
    cN
    rexrabdioph.1
    mapfzcons
    syl3anc
    adantrr
    @43
    @35
    @38
    @49
    @51
    @38
    @49
    @51
    @25
    @47
    vv
    @37
    @48
    @51
    @48
    @37
    @51
    @35
    @42
    @48
    @37
    wceq
    @52
    @53
    @10
    cn0
    @37
    cM
    cN
    rexrabdioph.1
    mapfzcons2
    syl2anc
    eqcomd
    @51
    wps
    vu
    @10
    @46
    @51
    @46
    @10
    @35
    @46
    @10
    wceq
    @43
    @10
    cn0
    @37
    cM
    cN
    rexrabdioph.1
    mapfzcons1
    adantl
    eqcomd
    #
    sbceq1d
    sbceqbid
    biimpd
    impr
    @43
    @35
    @50
    @38
    @54
    adantrr
    @32
    @49
    @50
    wa
    vb
    @44
    @2
    @11
    @44
    wceq
    #
    @31
    @49
    @13
    @50
    @55
    @29
    @47
    vv
    @30
    @48
    cM
    @11
    @44
    fveq1
    @55
    wps
    vu
    @12
    @46
    @11
    @44
    @7
    reseq1
    #
    sbceq1d
    sbceqbid
    @55
    @12
    @46
    @10
    @56
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    ex
    rexlimdva
    @0
    @32
    @40
    vb
    @2
    @0
    @11
    @2
    wcel
    #
    wa
    #
    @32
    @40
    @58
    @32
    wa
    #
    @30
    cn0
    wcel
    #
    @35
    @25
    vv
    @30
    wsbc
    #
    @40
    @58
    @60
    @32
    @57
    @1
    cn0
    @11
    wf
    cM
    @1
    wcel
    #
    @60
    @0
    @11
    cn0
    @1
    elmapi
    @0
    cM
    cn
    wcel
    @62
    @0
    cM
    cN
    c1
    caddc
    co
    #
    cn
    rexrabdioph.1
    cN
    nn0p1nn
    syl5eqel
    cM
    elfz1end
    sylib
    @1
    cn0
    cM
    @11
    ffvelrn
    syl2anr
    adantr
    @59
    @10
    @12
    @8
    @58
    @31
    @13
    simprr
    @57
    @12
    @8
    wcel
    @0
    @32
    @11
    cn0
    cM
    cN
    rexrabdioph.1
    mapfzcons1cl
    ad2antlr
    eqeltrd
    @59
    @61
    @31
    @58
    @31
    @13
    simprl
    @13
    @61
    @31
    wb
    @58
    @31
    @13
    @25
    @29
    vv
    @30
    wps
    vu
    @10
    @12
    dfsbcq
    sbcbidv
    ad2antll
    mpbird
    @39
    @35
    @61
    wa
    vc
    @30
    cn0
    @37
    @30
    wceq
    @38
    @61
    @35
    @25
    vv
    @37
    @30
    dfsbcq
    anbi2d
    rspcev
    syl12anc
    ex
    rexlimdva
    impbid
    syl5bb
    abbidv
    syl5eq
    @6
    @27
    vu
    va
    @8
    vu
    @8
    nfcv
    va
    @8
    nfcv
    @6
    va
    nfv
    @26
    vu
    vb
    cn0
    vu
    cn0
    nfcv
    @25
    vu
    vv
    @11
    vu
    @11
    nfcv
    wps
    vu
    @10
    nfsbc1v
    nfsbc
    nfrex
    vu
    va
    weq
    #
    @6
    @25
    vv
    cn0
    wrex
    @27
    @64
    wps
    @25
    vv
    cn0
    wps
    vu
    @10
    sbceq1a
    rexbidv
    @25
    @26
    vv
    vb
    cn0
    @25
    vb
    nfv
    @25
    vv
    @11
    nfsbc1v
    @25
    vv
    @11
    sbceq1a
    cbvrex
    syl6bb
    cbvrab
    @23
    @33
    va
    @21
    @31
    @13
    vb
    vt
    @2
    vt
    vb
    weq
    #
    @19
    @29
    vv
    @20
    @30
    cM
    @17
    @11
    fveq1
    @65
    wps
    vu
    @18
    @12
    @17
    @11
    @7
    reseq1
    sbceq1d
    sbceqbid
    rexrab
    abbii
    3eqtr4g
    @23
    @14
    va
    @13
    vb
    @22
    @3
    @21
    wph
    vt
    @2
    wps
    wph
    vv
    vu
    @20
    @18
    cM
    @17
    fvex
    @17
    @7
    vt
    vex
    resex
    vv
    cv
    @20
    wceq
    wps
    wch
    vu
    cv
    @18
    wceq
    wph
    rexrabdioph.2
    rexrabdioph.3
    sylan9bb
    sbc2ie
    rabbii
    rexeqi
    abbii
    syl6eq
    adantr
    @5
    @0
    cM
    cN
    cuz
    cfv
    #
    wcel
    #
    @4
    @15
    @16
    wcel
    @0
    @4
    simpl
    @0
    @67
    @4
    @0
    cM
    @63
    @66
    rexrabdioph.1
    @0
    cN
    cz
    wcel
    cN
    @66
    wcel
    @63
    @66
    wcel
    cN
    nn0z
    cN
    uzid
    cN
    cN
    peano2uz
    3syl
    syl5eqel
    adantr
    @0
    @4
    simpr
    vb
    va
    @3
    cM
    cN
    diophrex
    syl3anc
    eqeltrd
end
