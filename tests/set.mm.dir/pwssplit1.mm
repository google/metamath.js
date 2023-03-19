include "cmnd.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "pwssplit0.mm"
include "wa.mm"
include "cdif.mm"
include "c0g.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "cbs.mm"
include "cin.mm"
include "c0.mm"
include "cvv.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "ssexd.mm"
include "eqid.mm"
include "pwselbasb.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "fvex.mm"
include "fconst.mm"
include "a1i.mm"
include "simpl1.mm"
include "mndidcl.mm"
include "syl.mm"
include "snssd.mm"
include "fssd.mm"
include "disjdif.mm"
include "fun.mm"
include "syl21anc.mm"
include "simpl3.mm"
include "undif.mm"
include "sylib.mm"
include "unidm.mm"
include "feq23d.mm"
include "mpbid.mm"
include "simpl2.mm"
include "mpbird.mm"
include "cres.mm"
include "fvtresfn.mm"
include "resundir.mm"
include "wfn.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "incom.mm"
include "eqtri.mm"
include "fnconstg.mm"
include "ax-mp.mm"
include "fnresdisj.mm"
include "mp1i.mm"
include "mpbii.mm"
include "uneq12d.mm"
include "syl5eq.mm"
include "un0.mm"
include "syl6eq.mm"
include "eqtr2d.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem pwssplit1
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let cT: class T
  assume pwssplit1.y: |- Y = ( W ^s U )
  assume pwssplit1.z: |- Z = ( W ^s V )
  assume pwssplit1.b: |- B = ( Base ` Y )
  assume pwssplit1.c: |- C = ( Base ` Z )
  assume pwssplit1.f: |- F = ( x e. B |-> ( x |` V ) )

  disjoint Y x
  disjoint W x
  disjoint U x
  disjoint Z x
  disjoint V x
  disjoint B x
  disjoint C x
  disjoint X x
  disjoint Y a
  disjoint Y b
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint W a
  disjoint W b
  disjoint U a
  disjoint U b
  disjoint Z a
  disjoint Z b
  disjoint V a
  disjoint V b
  disjoint B a
  disjoint B b
  disjoint C a
  disjoint C b
  disjoint F a
  disjoint F b
  disjoint X a
  disjoint X b
  disjoint T x
  assert |- ( ( W e. Mnd /\ U e. X /\ V C_ U ) -> F : B -onto-> C )

  proof
    cW
    cmnd
    wcel
    #
    cU
    cX
    wcel
    #
    cV
    cU
    wss
    #
    w3a
    #
    cB
    cC
    cF
    wf
    va
    cv
    #
    vb
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vb
    cB
    wrex
    #
    va
    cC
    wral
    cB
    cC
    cF
    wfo
    vx
    cB
    cC
    cmnd
    cU
    cF
    cV
    cW
    cX
    cY
    cZ
    pwssplit1.y
    pwssplit1.z
    pwssplit1.b
    pwssplit1.c
    pwssplit1.f
    pwssplit0
    @3
    @8
    va
    cC
    @3
    @4
    cC
    wcel
    #
    wa
    #
    @4
    cU
    cV
    cdif
    #
    cW
    c0g
    cfv
    #
    csn
    #
    cxp
    #
    cun
    #
    cB
    wcel
    #
    @4
    @15
    cF
    cfv
    #
    wceq
    #
    @8
    @10
    @16
    cU
    cW
    cbs
    cfv
    #
    @15
    wf
    #
    @10
    cV
    @11
    cun
    #
    @19
    @19
    cun
    #
    @15
    wf
    #
    @20
    @10
    cV
    @19
    @4
    wf
    #
    @11
    @19
    @14
    wf
    cV
    @11
    cin
    #
    c0
    wceq
    #
    @23
    @3
    @9
    @24
    @3
    @0
    cV
    cvv
    wcel
    @9
    @24
    wb
    @0
    @1
    @2
    simp1
    @3
    cV
    cU
    cX
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    ssexd
    @19
    cW
    cV
    cC
    cmnd
    @4
    cZ
    cvv
    pwssplit1.z
    @19
    eqid
    #
    pwssplit1.c
    pwselbasb
    syl2anc
    biimpa
    #
    @10
    @11
    @13
    @19
    @14
    @11
    @13
    @14
    wf
    @10
    @11
    @12
    cW
    c0g
    fvex
    #
    fconst
    a1i
    @10
    @12
    @19
    @10
    @0
    @12
    @19
    wcel
    @0
    @1
    @2
    @9
    simpl1
    #
    @19
    cW
    @12
    @27
    @12
    eqid
    mndidcl
    syl
    snssd
    fssd
    @26
    @10
    cV
    cU
    disjdif
    #
    a1i
    cV
    @11
    @19
    @19
    @4
    @14
    fun
    syl21anc
    @10
    @21
    @22
    cU
    @19
    @15
    @10
    @2
    @21
    cU
    wceq
    @0
    @1
    @2
    @9
    simpl3
    cV
    cU
    undif
    sylib
    @22
    @19
    wceq
    @10
    @19
    unidm
    a1i
    feq23d
    mpbid
    @10
    @0
    @1
    @16
    @20
    wb
    @30
    @0
    @1
    @2
    @9
    simpl2
    @19
    cW
    cU
    cB
    cmnd
    @15
    cY
    cX
    pwssplit1.y
    @27
    pwssplit1.b
    pwselbasb
    syl2anc
    mpbird
    #
    @10
    @17
    @15
    cV
    cres
    #
    @4
    @10
    @16
    @17
    @33
    wceq
    @32
    vx
    cB
    cF
    cV
    @15
    pwssplit1.f
    fvtresfn
    syl
    @10
    @33
    @4
    c0
    cun
    #
    @4
    @10
    @33
    @4
    cV
    cres
    #
    @14
    cV
    cres
    #
    cun
    @34
    @4
    @14
    cV
    resundir
    @10
    @35
    @4
    @36
    c0
    @10
    @24
    @4
    cV
    wfn
    @35
    @4
    wceq
    @28
    cV
    @19
    @4
    ffn
    cV
    @4
    fnresdm
    3syl
    @10
    @11
    cV
    cin
    #
    c0
    wceq
    #
    @36
    c0
    wceq
    #
    @37
    @25
    c0
    @11
    cV
    incom
    @31
    eqtri
    @14
    @11
    wfn
    #
    @38
    @39
    wb
    @10
    @12
    cvv
    wcel
    @40
    @29
    @11
    @12
    cvv
    fnconstg
    ax-mp
    @11
    cV
    @14
    fnresdisj
    mp1i
    mpbii
    uneq12d
    syl5eq
    @4
    un0
    syl6eq
    eqtr2d
    @7
    @18
    vb
    @15
    cB
    @5
    @15
    wceq
    @6
    @17
    @4
    @5
    @15
    cF
    fveq2
    eqeq2d
    rspcev
    syl2anc
    ralrimiva
    vb
    va
    cB
    cC
    cF
    dffo3
    sylanbrc
end
