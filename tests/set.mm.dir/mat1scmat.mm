include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "crg.mm"
include "cscmat.mm"
include "co.mm"
include "wi.mm"
include "cv.mm"
include "csn.mm"
include "wex.mm"
include "hash1snb.mm"
include "cmat.mm"
include "cbs.mm"
include "wa.mm"
include "cur.mm"
include "cvsca.mm"
include "wrex.mm"
include "simpr.mm"
include "cop.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "mat1dimelbas.mm"
include "mpan2.mm"
include "cmulr.mm"
include "a1i.mm"
include "mat1dimid.mm"
include "sylan2.mm"
include "oveq2d.mm"
include "simpl.mm"
include "jctir.mm"
include "ringidcl.mm"
include "adantr.mm"
include "mat1dimscm.mm"
include "syl12anc.mm"
include "ringridm.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "3eqtrrd.mm"
include "eqtrd.mm"
include "ex.mm"
include "reximdva.mm"
include "sylbid.mm"
include "imp.mm"
include "cfn.mm"
include "snfi.mm"
include "scmatel.mm"
include "sylancr.mm"
include "mpbir2and.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "imbi12d.mm"
include "syl5ibr.mm"
include "exlimiv.mm"
include "syl6bi.mm"
include "3imp.mm"

theorem mat1scmat
  let cA: class A
  let cB: class B
  let cR: class R
  let cM: class M
  let cN: class N
  let cV: class V
  let ve: setvar e
  let vc: setvar c
  assume mat1scmat.a: |- A = ( N Mat R )
  assume mat1scmat.b: |- B = ( Base ` A )


  assert |- ( ( N e. V /\ ( # ` N ) = 1 /\ R e. Ring ) -> ( M e. B -> M e. ( N ScMat R ) ) )

  proof
    cN
    cV
    wcel
    #
    cN
    chash
    cfv
    c1
    wceq
    #
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    cM
    cN
    cR
    cscmat
    co
    #
    wcel
    #
    wi
    #
    @0
    @1
    cN
    ve
    cv
    #
    csn
    #
    wceq
    #
    ve
    wex
    @2
    @6
    wi
    #
    cN
    cV
    ve
    hash1snb
    @9
    @10
    ve
    @2
    @6
    @9
    cM
    @8
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    #
    cM
    @8
    cR
    cscmat
    co
    #
    wcel
    #
    wi
    @2
    @13
    @15
    @2
    @13
    wa
    #
    @15
    @13
    cM
    vc
    cv
    #
    @11
    cur
    cfv
    #
    @11
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vc
    cR
    cbs
    cfv
    #
    wrex
    #
    @2
    @13
    simpr
    @2
    @13
    @23
    @2
    @13
    cM
    @7
    @7
    cop
    #
    @17
    cop
    #
    csn
    #
    wceq
    #
    vc
    @22
    wrex
    #
    @23
    @2
    @7
    cvv
    wcel
    #
    @13
    @28
    wb
    ve
    vex
    #
    @11
    @22
    cR
    @7
    cM
    @24
    cvv
    vc
    @11
    eqid
    #
    @22
    eqid
    #
    @24
    eqid
    #
    mat1dimelbas
    mpan2
    @2
    @27
    @21
    vc
    @22
    @2
    @17
    @22
    wcel
    #
    wa
    #
    @27
    @21
    @35
    @27
    wa
    cM
    @26
    @20
    @35
    @27
    simpr
    @35
    @26
    @20
    wceq
    @27
    @35
    @20
    @17
    @24
    cR
    cur
    cfv
    #
    cop
    csn
    #
    @19
    co
    #
    @24
    @17
    @36
    cR
    cmulr
    cfv
    #
    co
    #
    cop
    #
    csn
    #
    @26
    @35
    @18
    @37
    @17
    @19
    @34
    @2
    @29
    @18
    @37
    wceq
    @29
    @34
    @30
    a1i
    @11
    @22
    cR
    @7
    @24
    cvv
    @31
    @32
    @33
    mat1dimid
    sylan2
    oveq2d
    @35
    @2
    @29
    wa
    @34
    @36
    @22
    wcel
    #
    @38
    @42
    wceq
    @35
    @2
    @29
    @2
    @34
    simpl
    @30
    jctir
    @2
    @34
    simpr
    @2
    @43
    @34
    @22
    cR
    @36
    @32
    @36
    eqid
    #
    ringidcl
    adantr
    @11
    @22
    cR
    @7
    @24
    cvv
    @17
    @36
    @31
    @32
    @33
    mat1dimscm
    syl12anc
    @35
    @41
    @25
    @35
    @40
    @17
    @24
    @22
    cR
    @39
    @36
    @17
    @32
    @39
    eqid
    @44
    ringridm
    opeq2d
    sneqd
    3eqtrrd
    adantr
    eqtrd
    ex
    reximdva
    sylbid
    imp
    @16
    @8
    cfn
    wcel
    @2
    @15
    @13
    @23
    wa
    wb
    @7
    snfi
    @2
    @13
    simpl
    @11
    @12
    cR
    @14
    @19
    @18
    @22
    cM
    @8
    crg
    vc
    @32
    @31
    @12
    eqid
    @18
    eqid
    @19
    eqid
    @14
    eqid
    scmatel
    sylancr
    mpbir2and
    ex
    @9
    @3
    @13
    @5
    @15
    @9
    cB
    @12
    cM
    @9
    cB
    cN
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    @12
    cB
    cA
    cbs
    cfv
    @46
    mat1scmat.b
    cA
    @45
    cbs
    mat1scmat.a
    fveq2i
    eqtri
    @9
    @45
    @11
    cbs
    cN
    @8
    cR
    cmat
    oveq1
    fveq2d
    syl5eq
    eleq2d
    @9
    @4
    @14
    cM
    cN
    @8
    cR
    cscmat
    oveq1
    eleq2d
    imbi12d
    syl5ibr
    exlimiv
    syl6bi
    3imp
end
