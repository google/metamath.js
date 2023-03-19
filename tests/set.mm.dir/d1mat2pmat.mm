include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cop.mm"
include "cfn.mm"
include "snfi.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "adantr.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "simp3.mm"
include "cmat.mm"
include "eqid.mm"
include "mat2pmatval.mm"
include "syl3anc.mm"
include "cvv.mm"
include "id.mm"
include "fvexd.mm"
include "3jca.mm"
include "adantl.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "mpt2sn.mm"
include "syl.mm"
include "wb.mm"
include "mpt2eq12.mm"
include "eqeq1d.mm"
include "anidms.mm"
include "mpbird.mm"
include "eqtrd.mm"

theorem d1mat2pmat
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cM: class M
  let cN: class N
  let cV: class V
  let vi: setvar i
  let vj: setvar j
  assume d1mat2pmat.t: |- T = ( N matToPolyMat R )
  assume d1mat2pmat.b: |- B = ( Base ` ( N Mat R ) )
  assume d1mat2pmat.p: |- P = ( Poly1 ` R )
  assume d1mat2pmat.s: |- S = ( algSc ` P )


  assert |- ( ( R e. V /\ ( N = { A } /\ A e. V ) /\ M e. B ) -> ( T ` M ) = { <. <. A , A >. , ( S ` ( A M A ) ) >. } )

  proof
    cR
    cV
    wcel
    #
    cN
    cA
    csn
    #
    wceq
    #
    cA
    cV
    wcel
    #
    wa
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cM
    cT
    cfv
    #
    vi
    vj
    cN
    cN
    vi
    cv
    #
    vj
    cv
    #
    cM
    co
    #
    cS
    cfv
    #
    cmpt2
    #
    cA
    cA
    cop
    cA
    cA
    cM
    co
    #
    cS
    cfv
    #
    cop
    csn
    #
    @6
    cN
    cfn
    wcel
    #
    @0
    @5
    @7
    @12
    wceq
    @4
    @0
    @16
    @5
    @2
    @16
    @3
    @2
    @16
    @1
    cfn
    wcel
    cA
    snfi
    cN
    @1
    cfn
    eleq1
    mpbiri
    adantr
    3ad2ant2
    @0
    @4
    @5
    simp1
    @0
    @4
    @5
    simp3
    vi
    vj
    cN
    cR
    cmat
    co
    #
    cB
    cP
    cR
    cS
    cT
    cM
    cN
    cV
    d1mat2pmat.t
    @17
    eqid
    d1mat2pmat.b
    d1mat2pmat.p
    d1mat2pmat.s
    mat2pmatval
    syl3anc
    @6
    @12
    @15
    wceq
    #
    vi
    vj
    @1
    @1
    @11
    cmpt2
    #
    @15
    wceq
    #
    @6
    @3
    @3
    @14
    cvv
    wcel
    #
    w3a
    #
    @20
    @4
    @0
    @22
    @5
    @3
    @22
    @2
    @3
    @3
    @3
    @21
    @3
    id
    #
    @23
    @3
    @13
    cS
    fvexd
    3jca
    adantl
    3ad2ant2
    vi
    vj
    cA
    cA
    @11
    cA
    @9
    cM
    co
    #
    cS
    cfv
    cvv
    @14
    @19
    cV
    cV
    @19
    eqid
    @8
    cA
    wceq
    @10
    @24
    cS
    @8
    cA
    @9
    cM
    oveq1
    fveq2d
    @9
    cA
    wceq
    @24
    @13
    cS
    @9
    cA
    cA
    cM
    oveq2
    fveq2d
    mpt2sn
    syl
    @4
    @0
    @18
    @20
    wb
    #
    @5
    @2
    @25
    @3
    @2
    @25
    @2
    @2
    wa
    @12
    @19
    @15
    vi
    vj
    cN
    cN
    @1
    @1
    @11
    mpt2eq12
    eqeq1d
    anidms
    adantr
    3ad2ant2
    mpbird
    eqtrd
end
