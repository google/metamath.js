include "cv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cbs.mm"
include "cfv.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "wcel.mm"
include "clt.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "eqid.mm"
include "coe1fsupp.mm"
include "wa.mm"
include "breq1.mm"
include "elrab.mm"
include "cvv.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fsuppmapnn0ub.mm"
include "sylan2.mm"
include "impancom.mm"
include "sylbi.mm"
include "mpcom.mm"

theorem coe1ae0
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let vn: setvar n
  let cF: class F
  let c.0: class .0.
  let vs: setvar s
  let va: setvar a
  assume coe1ae0.a: |- A = ( coe1 ` F )
  assume coe1ae0.b: |- B = ( Base ` P )
  assume coe1ae0.p: |- P = ( Poly1 ` R )
  assume coe1ae0.z: |- .0. = ( 0g ` R )

  disjoint A n
  disjoint A s
  disjoint n s
  disjoint .0. n
  disjoint .0. s
  disjoint A a
  disjoint a n
  disjoint a s
  disjoint R a
  disjoint .0. a
  assert |- ( F e. B -> E. s e. NN0 A. n e. NN0 ( s < n -> ( A ` n ) = .0. ) )

  proof
    cA
    va
    cv
    #
    c.0
    cfsupp
    wbr
    #
    va
    cR
    cbs
    cfv
    #
    cn0
    cmap
    co
    #
    crab
    wcel
    #
    cF
    cB
    wcel
    #
    vs
    cv
    vn
    cv
    #
    clt
    wbr
    @6
    cA
    cfv
    c.0
    wceq
    wi
    vn
    cn0
    wral
    vs
    cn0
    wrex
    #
    cA
    cB
    cP
    cR
    va
    cF
    @2
    c.0
    coe1ae0.a
    coe1ae0.b
    coe1ae0.p
    coe1ae0.z
    @2
    eqid
    coe1fsupp
    @4
    cA
    @3
    wcel
    #
    cA
    c.0
    cfsupp
    wbr
    #
    wa
    @5
    @7
    wi
    @1
    @9
    va
    cA
    @3
    @0
    cA
    c.0
    cfsupp
    breq1
    elrab
    @8
    @5
    @9
    @7
    @5
    @8
    c.0
    cvv
    wcel
    #
    @9
    @7
    wi
    @10
    @5
    c.0
    cR
    c0g
    cfv
    cvv
    coe1ae0.z
    cR
    c0g
    fvex
    eqeltri
    a1i
    vn
    @2
    vs
    cA
    cvv
    c.0
    fsuppmapnn0ub
    sylan2
    impancom
    sylbi
    mpcom
end
