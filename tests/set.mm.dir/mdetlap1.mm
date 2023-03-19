include "ccrg.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "co.mm"
include "cif.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cgsu.mm"
include "simp2.mm"
include "matmpt2.mm"
include "eqid.mm"
include "wtru.mm"
include "wa.mm"
include "simpr.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "wn.mm"
include "eqidd.mm"
include "ifeqda.mm"
include "trud.mm"
include "mpt2eq123i.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "syl.mm"
include "cbs.mm"
include "simp1.mm"
include "simpl3.mm"
include "syl6eleq.mm"
include "adantr.mm"
include "matecl.mm"
include "syl3anc.mm"
include "simp3.mm"
include "madugsum.mm"
include "eqtr4d.mm"

theorem mdetlap1
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let vj: setvar j
  let cI: class I
  let cK: class K
  let cM: class M
  let cN: class N
  let vi: setvar i
  assume mdetlap1.a: |- A = ( N Mat R )
  assume mdetlap1.b: |- B = ( Base ` A )
  assume mdetlap1.d: |- D = ( N maDet R )
  assume mdetlap1.k: |- K = ( N maAdju R )
  assume mdetlap1.t: |- .x. = ( .r ` R )

  disjoint .x. j
  disjoint A j
  disjoint B j
  disjoint I j
  disjoint K j
  disjoint M j
  disjoint N j
  disjoint R j
  disjoint A i
  disjoint i j
  disjoint B i
  disjoint I i
  disjoint M i
  disjoint N i
  disjoint R i
  assert |- ( ( R e. CRing /\ M e. B /\ I e. N ) -> ( D ` M ) = ( R gsum ( j e. N |-> ( ( I M j ) .x. ( j ( K ` M ) I ) ) ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    cI
    cN
    wcel
    #
    w3a
    #
    cM
    cD
    cfv
    #
    vi
    vj
    cN
    cN
    vi
    cv
    #
    cI
    wceq
    #
    cI
    vj
    cv
    #
    cM
    co
    #
    @5
    @7
    cM
    co
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    cR
    vj
    cN
    @8
    @7
    cI
    cM
    cK
    cfv
    co
    c.x
    co
    cmpt
    cgsu
    co
    @3
    @1
    @4
    @12
    wceq
    @0
    @1
    @2
    simp2
    #
    @1
    cM
    @11
    cD
    @1
    cM
    vi
    vj
    cN
    cN
    @9
    cmpt2
    @11
    cA
    cB
    cR
    vi
    vj
    cM
    cN
    mdetlap1.a
    mdetlap1.b
    matmpt2
    vi
    vj
    cN
    cN
    @10
    cN
    cN
    @9
    cN
    eqid
    #
    @14
    @10
    @9
    wceq
    wtru
    @6
    @8
    @9
    @9
    wtru
    @6
    wa
    #
    cI
    @5
    @7
    cM
    @15
    @5
    cI
    wtru
    @6
    simpr
    eqcomd
    oveq1d
    wtru
    @6
    wn
    wa
    @9
    eqidd
    ifeqda
    trud
    mpt2eq123i
    syl6eqr
    fveq2d
    syl
    @3
    cA
    cB
    cD
    cR
    c.x
    vj
    vi
    cK
    cR
    cbs
    cfv
    #
    cI
    cM
    cN
    @8
    mdetlap1.a
    mdetlap1.k
    mdetlap1.b
    mdetlap1.d
    mdetlap1.t
    @16
    eqid
    #
    @13
    @0
    @1
    @2
    simp1
    @3
    @7
    cN
    wcel
    #
    wa
    @2
    @18
    cM
    cA
    cbs
    cfv
    #
    wcel
    #
    @8
    @16
    wcel
    @0
    @1
    @2
    @18
    simpl3
    @3
    @18
    simpr
    @3
    @20
    @18
    @3
    cM
    cB
    @19
    @13
    mdetlap1.b
    syl6eleq
    adantr
    cA
    cR
    cI
    @7
    @16
    cM
    cN
    mdetlap1.a
    @17
    matecl
    syl3anc
    @0
    @1
    @2
    simp3
    madugsum
    eqtr4d
end
