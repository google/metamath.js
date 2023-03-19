include "cgrp.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "nmfval.mm"
include "wa.mm"
include "cxp.mm"
include "cres.mm"
include "oveqi.mm"
include "wceq.mm"
include "id.mm"
include "grpidcl.mm"
include "ovres.mm"
include "syl2anr.mm"
include "syl5req.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"

theorem nmfval2
  let vx: setvar x
  let cD: class D
  let cE: class E
  let cN: class N
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let cA: class A
  let vw: setvar w
  assume nmfval.n: |- N = ( norm ` W )
  assume nmfval.x: |- X = ( Base ` W )
  assume nmfval.z: |- .0. = ( 0g ` W )
  assume nmfval.d: |- D = ( dist ` W )
  assume nmfval.e: |- E = ( D |` ( X X. X ) )

  disjoint D x
  disjoint W x
  disjoint X x
  disjoint .0. x
  disjoint A x
  disjoint w x
  disjoint D w
  disjoint W w
  disjoint X w
  disjoint .0. w
  assert |- ( W e. Grp -> N = ( x e. X |-> ( x E .0. ) ) )

  proof
    cW
    cgrp
    wcel
    #
    cN
    vx
    cX
    vx
    cv
    #
    c.0
    cD
    co
    #
    cmpt
    vx
    cX
    @1
    c.0
    cE
    co
    #
    cmpt
    vx
    cD
    cN
    cW
    cX
    c.0
    nmfval.n
    nmfval.x
    nmfval.z
    nmfval.d
    nmfval
    @0
    vx
    cX
    @2
    @3
    @0
    @1
    cX
    wcel
    #
    wa
    @3
    @1
    c.0
    cD
    cX
    cX
    cxp
    cres
    #
    co
    #
    @2
    cE
    @5
    @1
    c.0
    nmfval.e
    oveqi
    @4
    @4
    c.0
    cX
    wcel
    @6
    @2
    wceq
    @0
    @4
    id
    cX
    cW
    c.0
    nmfval.x
    nmfval.z
    grpidcl
    @1
    c.0
    cX
    cX
    cD
    ovres
    syl2anr
    syl5req
    mpteq2dva
    syl5eq
end
