include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wral.mm"
include "simpr.mm"
include "gsummatr01lem1.mm"
include "jca.mm"
include "ovrspc2v.mm"
include "sylan.mm"
include "ex.mm"

theorem gsummatr01lem2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cG: class G
  let cK: class K
  let cL: class L
  let cN: class N
  let cX: class X
  let vr: setvar r
  let vn: setvar n
  let cB: class B
  let cS: class S
  let c.0: class .0.
  assume gsummatr01.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume gsummatr01.r: |- R = { r e. P | ( r ` K ) = L }

  disjoint A i
  disjoint A j
  disjoint i j
  disjoint G i
  disjoint G j
  disjoint K i
  disjoint K j
  disjoint K r
  disjoint L i
  disjoint L j
  disjoint L r
  disjoint N i
  disjoint N j
  disjoint P r
  disjoint Q r
  disjoint Q i
  disjoint Q j
  disjoint R i
  disjoint R j
  disjoint X i
  disjoint X j
  disjoint A n
  disjoint i n
  disjoint j n
  disjoint B i
  disjoint B j
  disjoint B n
  disjoint G n
  disjoint K n
  disjoint L n
  disjoint N n
  disjoint Q n
  disjoint R n
  disjoint S i
  disjoint S j
  disjoint S n
  disjoint .0. i
  disjoint .0. j
  disjoint .0. n
  assert |- ( ( Q e. R /\ X e. N ) -> ( A. i e. N A. j e. N ( i A j ) e. ( Base ` G ) -> ( X A ( Q ` X ) ) e. ( Base ` G ) ) )

  proof
    cQ
    cR
    wcel
    #
    cX
    cN
    wcel
    #
    wa
    #
    vi
    cv
    vj
    cv
    cA
    co
    cG
    cbs
    cfv
    #
    wcel
    vj
    cN
    wral
    vi
    cN
    wral
    #
    cX
    cX
    cQ
    cfv
    #
    cA
    co
    @3
    wcel
    #
    @2
    @1
    @5
    cN
    wcel
    #
    wa
    @4
    @6
    @2
    @1
    @7
    @0
    @1
    simpr
    cP
    cQ
    cR
    cK
    cL
    cN
    cX
    vr
    gsummatr01.p
    gsummatr01.r
    gsummatr01lem1
    jca
    vi
    vj
    cN
    cN
    @3
    cA
    cX
    @5
    ovrspc2v
    sylan
    ex
end
