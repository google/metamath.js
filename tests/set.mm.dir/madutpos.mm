include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "ctpos.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "weq.mm"
include "wo.mm"
include "cur.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt2.mm"
include "cmdat.mm"
include "eqid.mm"
include "tposmpt2.mm"
include "wb.mm"
include "orcom.mm"
include "a1i.mm"
include "ancom.mm"
include "ifbid.mm"
include "ovtpos.mm"
include "eqcomi.mm"
include "ifbieq12d.mm"
include "mpt2eq3dv.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "simpll.mm"
include "cbs.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "ad2antlr.mm"
include "w3a.mm"
include "crg.mm"
include "simp1ll.mm"
include "crngring.mm"
include "ringidcl.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "3syl.mm"
include "cxp.mm"
include "wf.mm"
include "cmap.mm"
include "matbas2i.mm"
include "elmapi.mm"
include "syl.mm"
include "fovrnda.mm"
include "3impb.mm"
include "matbas2d.mm"
include "mdettpos.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "mattposcl.mm"
include "adantl.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "maducoeval2.mm"
include "syl211anc.mm"
include "simplr.mm"
include "3eqtr4d.mm"
include "syl6eqr.mm"
include "ralrimivva.mm"
include "wfn.mm"
include "maduf.mm"
include "ffvelrnd.mm"
include "ffn.mm"
include "ffvelrnda.mm"
include "eqfnov2.mm"
include "mpbird.mm"

theorem madutpos
  let cA: class A
  let cB: class B
  let cR: class R
  let cJ: class J
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  let va: setvar a
  let wph: wff ph
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let cD: class D
  let cK: class K
  let cX: class X
  let cL: class L
  let c.x: class .x.
  assume maduf.a: |- A = ( N Mat R )
  assume maduf.j: |- J = ( N maAdju R )
  assume maduf.b: |- B = ( Base ` A )


  assert |- ( ( R e. CRing /\ M e. B ) -> ( J ` tpos M ) = tpos ( J ` M ) )

  proof
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    wa
    #
    cM
    ctpos
    #
    cJ
    cfv
    #
    cM
    cJ
    cfv
    #
    ctpos
    #
    wceq
    #
    va
    cv
    #
    vb
    cv
    #
    @4
    co
    #
    @8
    @9
    @6
    co
    #
    wceq
    #
    vb
    cN
    wral
    va
    cN
    wral
    #
    @2
    @12
    va
    vb
    cN
    cN
    @2
    @8
    cN
    wcel
    #
    @9
    cN
    wcel
    #
    wa
    #
    wa
    #
    @10
    @9
    @8
    @5
    co
    #
    @11
    @17
    vc
    vd
    cN
    cN
    vc
    vb
    weq
    #
    vd
    va
    weq
    #
    wo
    #
    @20
    @19
    wa
    #
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    #
    vc
    cv
    #
    vd
    cv
    #
    @3
    co
    #
    cif
    #
    cmpt2
    #
    cN
    cR
    cmdat
    co
    #
    cfv
    #
    vd
    vc
    cN
    cN
    @20
    @19
    wo
    #
    @19
    @20
    wa
    #
    @23
    @24
    cif
    #
    @27
    @26
    cM
    co
    #
    cif
    #
    cmpt2
    #
    @31
    cfv
    #
    @10
    @18
    @17
    @38
    ctpos
    #
    @31
    cfv
    #
    @32
    @39
    @17
    @40
    @30
    @31
    @17
    @40
    vc
    vd
    cN
    cN
    @37
    cmpt2
    @30
    vd
    vc
    cN
    cN
    @37
    @38
    @38
    eqid
    tposmpt2
    @17
    vc
    vd
    cN
    cN
    @37
    @29
    @17
    @33
    @21
    @35
    @36
    @25
    @28
    @33
    @21
    wb
    @17
    @20
    @19
    orcom
    a1i
    @17
    @34
    @22
    @23
    @24
    @34
    @22
    wb
    @17
    @19
    @20
    ancom
    a1i
    ifbid
    @36
    @28
    wceq
    @17
    @28
    @36
    @26
    @27
    cM
    ovtpos
    eqcomi
    a1i
    ifbieq12d
    mpt2eq3dv
    syl5eq
    fveq2d
    @17
    @0
    @38
    cB
    wcel
    @41
    @39
    wceq
    @0
    @1
    @16
    simpll
    #
    @17
    vd
    vc
    cA
    cB
    @37
    cR
    cR
    cbs
    cfv
    #
    cN
    ccrg
    maduf.a
    @43
    eqid
    #
    maduf.b
    @1
    cN
    cfn
    wcel
    #
    @0
    @16
    @1
    @45
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    maduf.a
    maduf.b
    matrcl
    simpld
    ad2antlr
    @42
    @17
    @27
    cN
    wcel
    #
    @26
    cN
    wcel
    #
    w3a
    #
    @33
    @35
    @36
    @43
    @48
    @0
    cR
    crg
    wcel
    #
    @35
    @43
    wcel
    @0
    @1
    @16
    @46
    @47
    simp1ll
    cR
    crngring
    @49
    @34
    @23
    @24
    @43
    @43
    cR
    @23
    @44
    @23
    eqid
    #
    ringidcl
    @43
    cR
    @24
    @44
    @24
    eqid
    #
    ring0cl
    ifcld
    3syl
    @17
    @46
    @47
    @36
    @43
    wcel
    @17
    @27
    @26
    @43
    cN
    cN
    cM
    @1
    cN
    cN
    cxp
    #
    @43
    cM
    wf
    #
    @0
    @16
    @1
    cM
    @43
    @52
    cmap
    co
    #
    wcel
    @53
    cA
    cB
    cR
    @43
    cM
    cN
    maduf.a
    @44
    maduf.b
    matbas2i
    cM
    @43
    @52
    elmapi
    syl
    ad2antlr
    fovrnda
    3impb
    ifcld
    matbas2d
    cA
    cB
    @31
    cR
    @38
    cN
    @31
    eqid
    #
    maduf.a
    maduf.b
    mdettpos
    syl2anc
    eqtr3d
    @17
    @0
    @3
    cB
    wcel
    #
    @14
    @15
    @10
    @32
    wceq
    @42
    @2
    @56
    @16
    @1
    @56
    @0
    cA
    cB
    cR
    cM
    cN
    maduf.a
    maduf.b
    mattposcl
    adantl
    #
    adantr
    @2
    @14
    @15
    simprl
    #
    @2
    @14
    @15
    simprr
    #
    cA
    cB
    @31
    cR
    @23
    vc
    @9
    @8
    cJ
    @3
    cN
    @24
    vd
    maduf.a
    @55
    maduf.j
    maduf.b
    @50
    @51
    maducoeval2
    syl211anc
    @17
    @0
    @1
    @15
    @14
    @18
    @39
    wceq
    @42
    @0
    @1
    @16
    simplr
    @59
    @58
    cA
    cB
    @31
    cR
    @23
    vd
    @8
    @9
    cJ
    cM
    cN
    @24
    vc
    maduf.a
    @55
    maduf.j
    maduf.b
    @50
    @51
    maducoeval2
    syl211anc
    3eqtr4d
    @8
    @9
    @5
    ovtpos
    syl6eqr
    ralrimivva
    @2
    @4
    @52
    wfn
    #
    @6
    @52
    wfn
    #
    @7
    @13
    wb
    @2
    @4
    @54
    wcel
    #
    @52
    @43
    @4
    wf
    @60
    @2
    @4
    cB
    wcel
    @62
    @2
    cB
    cB
    @3
    cJ
    @0
    cB
    cB
    cJ
    wf
    @1
    cA
    cB
    cR
    cJ
    cN
    maduf.a
    maduf.j
    maduf.b
    maduf
    #
    adantr
    @57
    ffvelrnd
    cA
    cB
    cR
    @43
    @4
    cN
    maduf.a
    @44
    maduf.b
    matbas2i
    syl
    @4
    @43
    @52
    elmapi
    @52
    @43
    @4
    ffn
    3syl
    @2
    @6
    @54
    wcel
    #
    @52
    @43
    @6
    wf
    @61
    @2
    @5
    cB
    wcel
    @6
    cB
    wcel
    @64
    @0
    cB
    cB
    cM
    cJ
    @63
    ffvelrnda
    cA
    cB
    cR
    @5
    cN
    maduf.a
    maduf.b
    mattposcl
    cA
    cB
    cR
    @43
    @6
    cN
    maduf.a
    @44
    maduf.b
    matbas2i
    3syl
    @6
    @43
    @52
    elmapi
    @52
    @43
    @6
    ffn
    3syl
    va
    vb
    cN
    cN
    @4
    @6
    eqfnov2
    syl2anc
    mpbird
end
