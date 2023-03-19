include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "ccnv.mm"
include "cv.mm"
include "cdif.mm"
include "cmpt.mm"
include "ctop.mm"
include "wceq.mm"
include "cldrcl.mm"
include "wf1o.mm"
include "opncldf1.mm"
include "simprd.mm"
include "syl.mm"
include "fveq1d.mm"
include "cldopn.mm"
include "difeq2.mm"
include "eqid.mm"
include "fvmptg.mm"
include "mpdan.mm"
include "eqtrd.mm"

theorem opncldf3
  let vu: setvar u
  let cB: class B
  let cF: class F
  let cJ: class J
  let cX: class X
  let cA: class A
  let vx: setvar x
  assume opncldf.1: |- X = U. J
  assume opncldf.2: |- F = ( u e. J |-> ( X \ u ) )

  disjoint J u
  disjoint X u
  disjoint A u
  disjoint B x
  disjoint F x
  disjoint u x
  disjoint J x
  disjoint X x
  assert |- ( B e. ( Clsd ` J ) -> ( `' F ` B ) = ( X \ B ) )

  proof
    cB
    cJ
    ccld
    cfv
    #
    wcel
    #
    cB
    cF
    ccnv
    #
    cfv
    cB
    vx
    @0
    cX
    vx
    cv
    #
    cdif
    #
    cmpt
    #
    cfv
    #
    cX
    cB
    cdif
    #
    @1
    cB
    @2
    @5
    @1
    cJ
    ctop
    wcel
    #
    @2
    @5
    wceq
    #
    cB
    cJ
    cldrcl
    @8
    cJ
    @0
    cF
    wf1o
    @9
    vx
    vu
    cF
    cJ
    cX
    opncldf.1
    opncldf.2
    opncldf1
    simprd
    syl
    fveq1d
    @1
    @7
    cJ
    wcel
    @6
    @7
    wceq
    cB
    cJ
    cX
    opncldf.1
    cldopn
    vx
    cB
    @4
    @7
    @0
    cJ
    @5
    @3
    cB
    cX
    difeq2
    @5
    eqid
    fvmptg
    mpdan
    eqtrd
end
