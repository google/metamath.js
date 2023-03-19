include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cdecpmat.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cn0.mm"
include "wral.mm"
include "wrex.mm"
include "cco1.mm"
include "cfv.mm"
include "c0g.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "adantl.mm"
include "simpl.mm"
include "simpr.mm"
include "eqid.mm"
include "pmatcoe1fsupp.mm"
include "syl3anc.mm"
include "cbs.mm"
include "wb.mm"
include "decpmatcl.mm"
include "3expa.mm"
include "jca.mm"
include "matring.mm"
include "ring0cl.mm"
include "3syl.mm"
include "adantr.mm"
include "eqmat.mm"
include "syl2anc.mm"
include "w3a.mm"
include "df-3an.mm"
include "decpmate.mm"
include "sylanbr.mm"
include "cmpt2.mm"
include "mat0op.mm"
include "syl5eq.mm"
include "syl.mm"
include "weq.mm"
include "eqidd.mm"
include "fvexd.mm"
include "ovmpt2d.mm"
include "eqeq12d.mm"
include "2ralbidva.mm"
include "bitrd.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "mpbird.mm"

theorem decpmataa0
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vs: setvar s
  let vi: setvar i
  let vj: setvar j
  let cK: class K
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  assume decpmate.p: |- P = ( Poly1 ` R )
  assume decpmate.c: |- C = ( N Mat P )
  assume decpmate.b: |- B = ( Base ` C )
  assume decpmatcl.a: |- A = ( N Mat R )
  assume decpmatfsupp.0: |- .0. = ( 0g ` A )

  disjoint B s
  disjoint B x
  disjoint s x
  disjoint M s
  disjoint M x
  disjoint N s
  disjoint N x
  disjoint R s
  disjoint R x
  disjoint .0. s
  disjoint .0. x
  disjoint B i
  disjoint B j
  disjoint i j
  disjoint K i
  disjoint K j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint R i
  disjoint R j
  disjoint V i
  disjoint V j
  disjoint B a
  disjoint B b
  disjoint B k
  disjoint a b
  disjoint a k
  disjoint a s
  disjoint a x
  disjoint b k
  disjoint b s
  disjoint b x
  disjoint k s
  disjoint k x
  disjoint M a
  disjoint M b
  disjoint M k
  disjoint N a
  disjoint N b
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint i s
  disjoint i x
  disjoint j s
  disjoint j x
  disjoint R a
  disjoint R b
  disjoint R k
  disjoint .0. i
  disjoint .0. j
  assert |- ( ( R e. Ring /\ M e. B ) -> E. s e. NN0 A. x e. NN0 ( s < x -> ( M decompPMat x ) = .0. ) )

  proof
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    wa
    #
    vs
    cv
    vx
    cv
    #
    clt
    wbr
    #
    cM
    @3
    cdecpmat
    co
    #
    c.0
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vs
    cn0
    wrex
    @4
    @3
    vi
    cv
    #
    vj
    cv
    #
    cM
    co
    cco1
    cfv
    cfv
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    wi
    #
    vx
    cn0
    wral
    #
    vs
    cn0
    wrex
    #
    @2
    cN
    cfn
    wcel
    #
    @0
    @1
    @17
    @1
    @18
    @0
    @1
    @18
    cP
    cvv
    wcel
    cC
    cB
    cP
    cN
    cM
    decpmate.c
    decpmate.b
    matrcl
    simpld
    adantl
    #
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    vx
    cB
    cC
    cP
    cR
    vi
    vj
    cM
    cN
    @12
    vs
    decpmate.p
    decpmate.c
    decpmate.b
    @12
    eqid
    #
    pmatcoe1fsupp
    syl3anc
    @2
    @8
    @16
    vs
    cn0
    @2
    @7
    @15
    vx
    cn0
    @2
    @3
    cn0
    wcel
    #
    wa
    #
    @6
    @14
    @4
    @23
    @6
    @9
    @10
    @5
    co
    #
    @9
    @10
    c.0
    co
    #
    wceq
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    @14
    @23
    @5
    cA
    cbs
    cfv
    #
    wcel
    #
    c.0
    @28
    wcel
    #
    @6
    @27
    wb
    @0
    @1
    @22
    @29
    cA
    cB
    cC
    @28
    cP
    cR
    @3
    cM
    cN
    crg
    decpmate.p
    decpmate.c
    decpmate.b
    decpmatcl.a
    @28
    eqid
    #
    decpmatcl
    3expa
    @2
    @30
    @22
    @2
    @18
    @0
    wa
    #
    cA
    crg
    wcel
    @30
    @2
    @18
    @0
    @19
    @20
    jca
    #
    cA
    cR
    cN
    decpmatcl.a
    matring
    @28
    cA
    c.0
    @31
    decpmatfsupp.0
    ring0cl
    3syl
    adantr
    cA
    @28
    cR
    vi
    vj
    cN
    @5
    c.0
    decpmatcl.a
    @31
    eqmat
    syl2anc
    @23
    @26
    @13
    vi
    vj
    cN
    cN
    @23
    @9
    cN
    wcel
    #
    @10
    cN
    wcel
    #
    wa
    #
    wa
    #
    @24
    @11
    @25
    @12
    @23
    @0
    @1
    @22
    w3a
    @36
    @24
    @11
    wceq
    @0
    @1
    @22
    df-3an
    cB
    cC
    cP
    cR
    @9
    @10
    @3
    cM
    cN
    crg
    decpmate.p
    decpmate.c
    decpmate.b
    decpmate
    sylanbr
    @37
    va
    vb
    @9
    @10
    cN
    cN
    @12
    @12
    c.0
    cvv
    @37
    @32
    c.0
    va
    vb
    cN
    cN
    @12
    cmpt2
    #
    wceq
    @23
    @32
    @36
    @2
    @32
    @22
    @33
    adantr
    adantr
    @32
    c.0
    cA
    c0g
    cfv
    @38
    decpmatfsupp.0
    cA
    cR
    va
    vb
    cN
    @12
    decpmatcl.a
    @21
    mat0op
    syl5eq
    syl
    @37
    va
    vi
    weq
    vb
    vj
    weq
    wa
    wa
    @12
    eqidd
    @36
    @34
    @23
    @34
    @35
    simpl
    adantl
    @36
    @35
    @23
    @34
    @35
    simpr
    adantl
    @37
    cR
    c0g
    fvexd
    ovmpt2d
    eqeq12d
    2ralbidva
    bitrd
    imbi2d
    ralbidva
    rexbidv
    mpbird
end
