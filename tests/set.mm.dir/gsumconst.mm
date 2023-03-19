include "cmnd.mm"
include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "c0.mm"
include "wceq.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cn.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wa.mm"
include "cc0.mm"
include "c0g.mm"
include "simpl3.mm"
include "eqid.mm"
include "mulg0.mm"
include "syl.mm"
include "fveq2.mm"
include "adantl.mm"
include "hash0.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "mpteq1.mm"
include "mpt0.mm"
include "oveq2d.mm"
include "gsum0.mm"
include "3eqtr4rd.mm"
include "ex.mm"
include "cplusg.mm"
include "ccom.mm"
include "cseq.mm"
include "csn.mm"
include "cxp.mm"
include "cuz.mm"
include "simprl.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "simpr.mm"
include "adantr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "wf.mm"
include "f1of.mm"
include "ad2antll.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "eqidd.mm"
include "fmptco.mm"
include "fveq1d.mm"
include "elfznn.mm"
include "fvconst2g.mm"
include "syl2an.mm"
include "3eqtr4d.mm"
include "seqfveq.mm"
include "csupp.mm"
include "ccntz.mm"
include "simpl1.mm"
include "simpl2.mm"
include "fmptd.mm"
include "wss.mm"
include "crn.mm"
include "wb.mm"
include "elcntzsn.mm"
include "mpbir2and.mm"
include "snssd.mm"
include "snidg.mm"
include "frn.mm"
include "cntzidss.mm"
include "wf1.mm"
include "f1of1.mm"
include "cdm.mm"
include "suppssdm.mm"
include "dmmptss.mm"
include "a1i.mm"
include "syl5ss.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "sseqtr4d.mm"
include "gsumval3.mm"
include "mulgnn.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "wo.mm"
include "fz1f1o.mm"
include "3ad2ant2.mm"
include "mpjaod.mm"

theorem gsumconst
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let vk: setvar k
  let cG: class G
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  assume gsumconst.b: |- B = ( Base ` G )
  assume gsumconst.m: |- .x. = ( .g ` G )

  disjoint A k
  disjoint B k
  disjoint G k
  disjoint X k
  disjoint f k
  disjoint f x
  disjoint A f
  disjoint k x
  disjoint A x
  disjoint B f
  disjoint B x
  disjoint G f
  disjoint G x
  disjoint .x. f
  disjoint X f
  disjoint X x
  assert |- ( ( G e. Mnd /\ A e. Fin /\ X e. B ) -> ( G gsum ( k e. A |-> X ) ) = ( ( # ` A ) .x. X ) )

  proof
    cG
    cmnd
    wcel
    #
    cA
    cfn
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    cA
    c0
    wceq
    #
    cG
    vk
    cA
    cX
    cmpt
    #
    cgsu
    co
    #
    cA
    chash
    cfv
    #
    cX
    c.x
    co
    #
    wceq
    #
    @7
    cn
    wcel
    #
    c1
    @7
    cfz
    co
    #
    cA
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    wa
    #
    @3
    @4
    @9
    @3
    @4
    wa
    #
    cc0
    cX
    c.x
    co
    #
    cG
    c0g
    cfv
    #
    @8
    @6
    @16
    @2
    @17
    @18
    wceq
    @0
    @1
    @2
    @4
    simpl3
    cB
    c.x
    cG
    cX
    @18
    gsumconst.b
    @18
    eqid
    #
    gsumconst.m
    mulg0
    syl
    @16
    @7
    cc0
    cX
    c.x
    @16
    @7
    c0
    chash
    cfv
    #
    cc0
    @4
    @7
    @20
    wceq
    @3
    cA
    c0
    chash
    fveq2
    adantl
    hash0
    syl6eq
    oveq1d
    @16
    @6
    cG
    c0
    cgsu
    co
    @18
    @16
    @5
    c0
    cG
    cgsu
    @16
    @5
    vk
    c0
    cX
    cmpt
    #
    c0
    @4
    @5
    @21
    wceq
    @3
    vk
    cA
    c0
    cX
    mpteq1
    adantl
    vk
    cX
    mpt0
    syl6eq
    oveq2d
    cG
    @18
    @19
    gsum0
    syl6eq
    3eqtr4rd
    ex
    @3
    @10
    @14
    @9
    @3
    @10
    wa
    @13
    @9
    vf
    @3
    @10
    @13
    @9
    @3
    @10
    @13
    wa
    #
    wa
    #
    @7
    cG
    cplusg
    cfv
    #
    @5
    @12
    ccom
    #
    c1
    cseq
    cfv
    @7
    @24
    cn
    cX
    csn
    #
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    @6
    @8
    @23
    @24
    vx
    @25
    @27
    c1
    @7
    @23
    @7
    cn
    c1
    cuz
    cfv
    @3
    @10
    @13
    simprl
    #
    nnuz
    syl6eleq
    @23
    vx
    cv
    #
    @11
    wcel
    #
    wa
    #
    @31
    vx
    @11
    cX
    cmpt
    #
    cfv
    #
    cX
    @31
    @25
    cfv
    #
    @31
    @27
    cfv
    #
    @33
    @32
    @2
    @35
    cX
    wceq
    @23
    @32
    simpr
    @23
    @2
    @32
    @0
    @1
    @2
    @22
    simpl3
    #
    adantr
    vx
    @11
    cX
    cB
    @34
    @34
    eqid
    fvmpt2
    syl2anc
    @23
    @36
    @35
    wceq
    @32
    @23
    @31
    @25
    @34
    @23
    vx
    vk
    @11
    cA
    @31
    @12
    cfv
    #
    cX
    cX
    @12
    @5
    @23
    @11
    cA
    @31
    @12
    @13
    @11
    cA
    @12
    wf
    @3
    @10
    @11
    cA
    @12
    f1of
    ad2antll
    #
    ffvelrnda
    @23
    vx
    @11
    cA
    @12
    @40
    feqmptd
    @23
    @5
    eqidd
    vk
    cv
    #
    @39
    wceq
    cX
    eqidd
    fmptco
    fveq1d
    adantr
    @23
    @2
    @31
    cn
    wcel
    @37
    cX
    wceq
    @32
    @38
    @31
    @7
    elfznn
    cn
    cX
    @31
    cB
    fvconst2g
    syl2an
    3eqtr4d
    seqfveq
    @23
    cA
    cB
    @24
    @5
    cG
    @12
    @7
    cfn
    @25
    @18
    csupp
    co
    #
    @18
    cG
    ccntz
    cfv
    #
    gsumconst.b
    @19
    @24
    eqid
    #
    @43
    eqid
    #
    @0
    @1
    @2
    @22
    simpl1
    @0
    @1
    @2
    @22
    simpl2
    @23
    vk
    cA
    cX
    cB
    @5
    @23
    @2
    @41
    cA
    wcel
    #
    @38
    adantr
    @5
    eqid
    #
    fmptd
    @23
    @26
    @26
    @43
    cfv
    #
    wss
    @5
    crn
    #
    @26
    wss
    #
    @49
    @49
    @43
    cfv
    wss
    @23
    cX
    @48
    @23
    cX
    @48
    wcel
    #
    @2
    cX
    cX
    @24
    co
    #
    @52
    wceq
    #
    @38
    @23
    @52
    eqidd
    @23
    @2
    @51
    @2
    @53
    wa
    wb
    @38
    cB
    @24
    cG
    cX
    cX
    @43
    gsumconst.b
    @44
    @45
    elcntzsn
    syl
    mpbir2and
    snssd
    @23
    cA
    @26
    @5
    wf
    @50
    @23
    vk
    cA
    cX
    @26
    @5
    @23
    cX
    @26
    wcel
    #
    @46
    @23
    @2
    @54
    @38
    cX
    cB
    snidg
    syl
    adantr
    @47
    fmptd
    cA
    @26
    @5
    frn
    syl
    @26
    @49
    cG
    @43
    @45
    cntzidss
    syl2anc
    @30
    @13
    @11
    cA
    @12
    wf1
    @3
    @10
    @11
    cA
    @12
    f1of1
    ad2antll
    @23
    @5
    @18
    csupp
    co
    #
    cA
    @12
    crn
    #
    @23
    @55
    @5
    cdm
    #
    cA
    @5
    @18
    suppssdm
    @57
    cA
    wss
    @23
    vk
    cA
    cX
    @5
    @47
    dmmptss
    a1i
    syl5ss
    @13
    @56
    cA
    wceq
    #
    @3
    @10
    @13
    @11
    cA
    @12
    wfo
    @58
    @11
    cA
    @12
    f1ofo
    @11
    cA
    @12
    forn
    syl
    ad2antll
    sseqtr4d
    @42
    eqid
    gsumval3
    @23
    @10
    @2
    @8
    @29
    wceq
    @30
    @38
    cB
    @24
    @28
    c.x
    cG
    @7
    cX
    gsumconst.b
    @44
    gsumconst.m
    @28
    eqid
    mulgnn
    syl2anc
    3eqtr4d
    expr
    exlimdv
    expimpd
    @1
    @0
    @4
    @15
    wo
    @2
    cA
    vf
    fz1f1o
    3ad2ant2
    mpjaod
end
