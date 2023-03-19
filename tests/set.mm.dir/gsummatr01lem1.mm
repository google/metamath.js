include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "simplbi.mm"
include "csymg.mm"
include "eqid.mm"
include "symgfv.mm"
include "sylan.mm"

theorem gsummatr01lem1
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cK: class K
  let cL: class L
  let cN: class N
  let cX: class X
  let vr: setvar r
  let cA: class A
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cB: class B
  let cG: class G
  let cS: class S
  let c.0: class .0.
  assume gsummatr01.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume gsummatr01.r: |- R = { r e. P | ( r ` K ) = L }

  disjoint K r
  disjoint L r
  disjoint P r
  disjoint Q r
  disjoint A i
  disjoint A j
  disjoint A n
  disjoint i j
  disjoint i n
  disjoint j n
  disjoint B i
  disjoint B j
  disjoint B n
  disjoint G i
  disjoint G j
  disjoint G n
  disjoint K i
  disjoint K j
  disjoint K n
  disjoint L i
  disjoint L j
  disjoint L n
  disjoint N i
  disjoint N j
  disjoint N n
  disjoint Q i
  disjoint Q j
  disjoint Q n
  disjoint R i
  disjoint R j
  disjoint R n
  disjoint S i
  disjoint S j
  disjoint S n
  disjoint X i
  disjoint X j
  disjoint .0. i
  disjoint .0. j
  disjoint .0. n
  assert |- ( ( Q e. R /\ X e. N ) -> ( Q ` X ) e. N )

  proof
    cQ
    cR
    wcel
    #
    cQ
    cP
    wcel
    #
    cX
    cN
    wcel
    cX
    cQ
    cfv
    cN
    wcel
    @0
    @1
    cK
    cQ
    cfv
    #
    cL
    wceq
    #
    cK
    vr
    cv
    #
    cfv
    #
    cL
    wceq
    @3
    vr
    cQ
    cP
    cR
    @4
    cQ
    wceq
    @5
    @2
    cL
    cK
    @4
    cQ
    fveq1
    eqeq1d
    gsummatr01.r
    elrab2
    simplbi
    cN
    cP
    cQ
    cN
    csymg
    cfv
    #
    cX
    @6
    eqid
    gsummatr01.p
    symgfv
    sylan
end
