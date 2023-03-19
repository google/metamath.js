include "clmod.mm"
include "wcel.mm"
include "crn.mm"
include "wss.mm"
include "w3a.mm"
include "cvv.mm"
include "clindf.mm"
include "wbr.mm"
include "wi.mm"
include "rellindf.mm"
include "brrelexi.mm"
include "a1i.mm"
include "wb.mm"
include "wa.mm"
include "cdm.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "clspn.mm"
include "wn.mm"
include "csca.mm"
include "c0g.mm"
include "wral.mm"
include "simpr.mm"
include "eqid.mm"
include "ressbasss.mm"
include "fss.mm"
include "sylancl.mm"
include "wfn.mm"
include "ffn.mm"
include "adantl.mm"
include "simp3.mm"
include "wceq.mm"
include "lssss.mm"
include "3ad2ant2.mm"
include "ressbas2.mm"
include "syl.mm"
include "sseqtrd.mm"
include "adantr.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "impbida.mm"
include "simpl2.mm"
include "resssca.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "ressvsca.mm"
include "oveqd.mm"
include "simpl1.mm"
include "imassrn.mm"
include "simpl3.mm"
include "syl5ss.mm"
include "lsslsp.mm"
include "syl3anc.mm"
include "eleq12d.mm"
include "notbid.mm"
include "raleqbidv.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "cress.mm"
include "ovex.mm"
include "eqeltri.mm"
include "islindf.mm"
include "sylan.mm"
include "3ad2antl1.mm"
include "3bitr4d.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem lsslindf
  let cS: class S
  let cU: class U
  let cF: class F
  let cW: class W
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume lsslindf.u: |- U = ( LSubSp ` W )
  assume lsslindf.x: |- X = ( W |`s S )


  assert |- ( ( W e. LMod /\ S e. U /\ ran F C_ S ) -> ( F LIndF X <-> F LIndF W ) )

  proof
    cW
    clmod
    wcel
    #
    cS
    cU
    wcel
    #
    cF
    crn
    #
    cS
    wss
    #
    w3a
    #
    cF
    cvv
    wcel
    #
    cF
    cX
    clindf
    wbr
    #
    cF
    cW
    clindf
    wbr
    #
    @6
    @5
    wi
    @4
    cF
    cX
    clindf
    rellindf
    brrelexi
    a1i
    @7
    @5
    wi
    @4
    cF
    cW
    clindf
    rellindf
    brrelexi
    a1i
    @4
    @5
    @6
    @7
    wb
    @4
    @5
    wa
    #
    cF
    cdm
    #
    cX
    cbs
    cfv
    #
    cF
    wf
    #
    vk
    cv
    #
    vx
    cv
    #
    cF
    cfv
    #
    cX
    cvsca
    cfv
    #
    co
    #
    cF
    @9
    @13
    csn
    cdif
    #
    cima
    #
    cX
    clspn
    cfv
    #
    cfv
    #
    wcel
    #
    wn
    #
    vk
    cX
    csca
    cfv
    #
    cbs
    cfv
    #
    @23
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wral
    #
    vx
    @9
    wral
    #
    wa
    #
    @9
    cW
    cbs
    cfv
    #
    cF
    wf
    #
    @12
    @14
    cW
    cvsca
    cfv
    #
    co
    #
    @18
    cW
    clspn
    cfv
    #
    cfv
    #
    wcel
    #
    wn
    #
    vk
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    @39
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wral
    #
    vx
    @9
    wral
    #
    wa
    #
    @6
    @7
    @8
    @11
    @32
    @29
    @45
    @4
    @11
    @32
    wb
    @5
    @4
    @11
    @32
    @4
    @11
    wa
    @11
    @10
    @31
    wss
    @32
    @4
    @11
    simpr
    cS
    @31
    cX
    cW
    lsslindf.x
    @31
    eqid
    #
    ressbasss
    @9
    @10
    @31
    cF
    fss
    sylancl
    @4
    @32
    wa
    cF
    @9
    wfn
    #
    @2
    @10
    wss
    #
    @11
    @32
    @48
    @4
    @9
    @31
    cF
    ffn
    adantl
    @4
    @49
    @32
    @4
    @2
    cS
    @10
    @0
    @1
    @3
    simp3
    @4
    cS
    @31
    wss
    #
    cS
    @10
    wceq
    @1
    @0
    @50
    @3
    cU
    cS
    @31
    cW
    @47
    lsslindf.u
    lssss
    3ad2ant2
    cS
    @31
    cX
    cW
    lsslindf.x
    @47
    ressbas2
    syl
    sseqtrd
    adantr
    @9
    @10
    cF
    df-f
    sylanbrc
    impbida
    adantr
    @8
    @28
    @44
    vx
    @9
    @8
    @22
    @38
    vk
    @27
    @43
    @8
    @24
    @40
    @26
    @42
    @8
    @23
    @39
    cbs
    @8
    @1
    @23
    @39
    wceq
    @0
    @1
    @3
    @5
    simpl2
    #
    @1
    @39
    @23
    cS
    @39
    cW
    cX
    cU
    lsslindf.x
    @39
    eqid
    #
    resssca
    eqcomd
    syl
    #
    fveq2d
    @8
    @25
    @41
    @8
    @23
    @39
    c0g
    @53
    fveq2d
    sneqd
    difeq12d
    @8
    @21
    @37
    @8
    @16
    @34
    @20
    @36
    @8
    @15
    @33
    @12
    @14
    @8
    @1
    @15
    @33
    wceq
    @51
    @1
    @33
    @15
    cS
    @33
    cW
    cX
    cU
    lsslindf.x
    @33
    eqid
    #
    ressvsca
    eqcomd
    syl
    oveqd
    @8
    @36
    @20
    @8
    @0
    @1
    @18
    cS
    wss
    @36
    @20
    wceq
    @0
    @1
    @3
    @5
    simpl1
    @51
    @8
    @18
    @2
    cS
    cF
    @17
    imassrn
    @0
    @1
    @3
    @5
    simpl3
    syl5ss
    cS
    @18
    cU
    @35
    @19
    cW
    cX
    lsslindf.x
    @35
    eqid
    #
    @19
    eqid
    #
    lsslindf.u
    lsslsp
    syl3anc
    eqcomd
    eleq12d
    notbid
    raleqbidv
    ralbidv
    anbi12d
    @4
    cX
    cvv
    wcel
    #
    @5
    @6
    @30
    wb
    @57
    @4
    cX
    cW
    cS
    cress
    co
    cvv
    lsslindf.x
    cW
    cS
    cress
    ovex
    eqeltri
    a1i
    vx
    @10
    @23
    @15
    vk
    cF
    @19
    @24
    cX
    cvv
    cvv
    @25
    @10
    eqid
    @15
    eqid
    @56
    @23
    eqid
    @24
    eqid
    @25
    eqid
    islindf
    sylan
    @0
    @1
    @5
    @7
    @46
    wb
    @3
    vx
    @31
    @39
    @33
    vk
    cF
    @35
    @40
    cW
    cvv
    clmod
    @41
    @47
    @54
    @55
    @52
    @40
    eqid
    @41
    eqid
    islindf
    3ad2antl1
    3bitr4d
    ex
    pm5.21ndd
end
