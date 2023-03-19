include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c0.mm"
include "cgsu.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "chash.mm"
include "cexp.mm"
include "c0g.mm"
include "eqid.mm"
include "gsum0.mm"
include "cop.mm"
include "csn.mm"
include "wceq.mm"
include "symg1bas.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "wi.mm"
include "elsni.mm"
include "cid.mm"
include "cres.mm"
include "reseq2i.mm"
include "snex.mm"
include "snid.mm"
include "eqeltri.mm"
include "symgid.mm"
include "mp1i.mm"
include "cxp.mm"
include "restidsing.mm"
include "xpsng.mm"
include "anidms.mm"
include "syl5eq.mm"
include "3eqtr3a.mm"
include "adantr.mm"
include "id.mm"
include "eqcoms.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "syl.mm"
include "mpcom.mm"
include "syl5req.mm"
include "fveq2d.mm"
include "cvv.mm"
include "cword.mm"
include "wrd0.mm"
include "pm3.2i.mm"
include "cpmtr.mm"
include "crn.mm"
include "fveq2i.mm"
include "pmtrsn.mm"
include "eqtri.mm"
include "rneqi.mm"
include "rn0.mm"
include "eqtr2i.mm"
include "psgnvalii.mm"
include "cc0.mm"
include "hash0.mm"
include "oveq2i.mm"
include "cc.mm"
include "neg1cn.mm"
include "exp0.mm"
include "ax-mp.mm"
include "a1i.mm"
include "3eqtrd.mm"

theorem psgnsn
  let cA: class A
  let cB: class B
  let cD: class D
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  assume psgnsn.0: |- D = { A }
  assume psgnsn.g: |- G = ( SymGrp ` D )
  assume psgnsn.b: |- B = ( Base ` G )
  assume psgnsn.n: |- N = ( pmSgn ` D )


  assert |- ( ( A e. V /\ X e. B ) -> ( N ` X ) = 1 )

  proof
    cA
    cV
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cN
    cfv
    cG
    c0
    cgsu
    co
    #
    cN
    cfv
    #
    c1
    cneg
    #
    c0
    chash
    cfv
    #
    cexp
    co
    #
    c1
    @2
    cX
    @3
    cN
    @2
    @3
    cG
    c0g
    cfv
    #
    cX
    cG
    @8
    @8
    eqid
    gsum0
    cX
    cA
    cA
    cop
    csn
    #
    csn
    #
    wcel
    #
    @2
    @8
    cX
    wceq
    #
    @0
    @1
    @11
    @0
    cB
    @10
    cX
    cD
    cB
    cG
    cA
    cV
    psgnsn.g
    psgnsn.b
    psgnsn.0
    symg1bas
    eleq2d
    biimpa
    @11
    cX
    @9
    wceq
    #
    @2
    @12
    wi
    cX
    @9
    elsni
    @13
    @2
    @12
    @2
    @13
    @8
    @9
    cX
    @0
    @8
    @9
    wceq
    @1
    @0
    cid
    cD
    cres
    #
    cid
    cA
    csn
    #
    cres
    #
    @8
    @9
    cD
    @15
    cid
    psgnsn.0
    reseq2i
    cD
    @15
    csn
    #
    wcel
    @14
    @8
    wceq
    @0
    cD
    @15
    @17
    psgnsn.0
    @15
    cA
    snex
    #
    snid
    eqeltri
    cD
    cG
    @17
    psgnsn.g
    symgid
    mp1i
    @0
    @16
    @15
    @15
    cxp
    #
    @9
    cA
    restidsing
    @0
    @19
    @9
    wceq
    cA
    cA
    cV
    cV
    xpsng
    anidms
    syl5eq
    3eqtr3a
    adantr
    @9
    cX
    wceq
    #
    @9
    cX
    @20
    id
    eqcoms
    sylan9eqr
    ex
    syl
    mpcom
    syl5req
    fveq2d
    cD
    cvv
    wcel
    #
    c0
    c0
    cword
    wcel
    #
    wa
    @4
    @7
    wceq
    @2
    @21
    @22
    cD
    @15
    cvv
    psgnsn.0
    @18
    eqeltri
    c0
    wrd0
    pm3.2i
    cD
    c0
    cG
    cN
    cvv
    c0
    psgnsn.g
    cD
    cpmtr
    cfv
    #
    crn
    c0
    crn
    c0
    @23
    c0
    @23
    @15
    cpmtr
    cfv
    c0
    cD
    @15
    cpmtr
    psgnsn.0
    fveq2i
    cA
    pmtrsn
    eqtri
    rneqi
    rn0
    eqtr2i
    psgnsn.n
    psgnvalii
    mp1i
    @7
    c1
    wceq
    @2
    @7
    @5
    cc0
    cexp
    co
    #
    c1
    @6
    cc0
    @5
    cexp
    hash0
    oveq2i
    @5
    cc
    wcel
    @24
    c1
    wceq
    neg1cn
    @5
    exp0
    ax-mp
    eqtri
    a1i
    3eqtrd
end
