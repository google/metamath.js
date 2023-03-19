include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "cdif.mm"
include "ccld.mm"
include "cfv.mm"
include "wceq.mm"
include "simpr.mm"
include "opncld.mm"
include "cv.mm"
include "difeq2.mm"
include "fvmptg.mm"
include "syl2anc.mm"

theorem opncldf2
  let vu: setvar u
  let cA: class A
  let cF: class F
  let cJ: class J
  let cX: class X
  let cB: class B
  let vx: setvar x
  assume opncldf.1: |- X = U. J
  assume opncldf.2: |- F = ( u e. J |-> ( X \ u ) )

  disjoint A u
  disjoint J u
  disjoint X u
  disjoint B x
  disjoint F x
  disjoint u x
  disjoint J x
  disjoint X x
  assert |- ( ( J e. Top /\ A e. J ) -> ( F ` A ) = ( X \ A ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cJ
    wcel
    #
    wa
    @1
    cX
    cA
    cdif
    #
    cJ
    ccld
    cfv
    #
    wcel
    cA
    cF
    cfv
    @2
    wceq
    @0
    @1
    simpr
    cA
    cJ
    cX
    opncldf.1
    opncld
    vu
    cA
    cX
    vu
    cv
    #
    cdif
    @2
    cJ
    @3
    cF
    @4
    cA
    cX
    difeq2
    opncldf.2
    fvmptg
    syl2anc
end
