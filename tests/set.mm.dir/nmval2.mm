include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "nmval.mm"
include "adantl.mm"
include "cxp.mm"
include "cres.mm"
include "oveqi.mm"
include "id.mm"
include "grpidcl.mm"
include "ovres.mm"
include "syl2anr.mm"
include "syl5req.mm"
include "eqtrd.mm"

theorem nmval2
  let cA: class A
  let cD: class D
  let cE: class E
  let cN: class N
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vw: setvar w
  assume nmfval.n: |- N = ( norm ` W )
  assume nmfval.x: |- X = ( Base ` W )
  assume nmfval.z: |- .0. = ( 0g ` W )
  assume nmfval.d: |- D = ( dist ` W )
  assume nmfval.e: |- E = ( D |` ( X X. X ) )


  assert |- ( ( W e. Grp /\ A e. X ) -> ( N ` A ) = ( A E .0. ) )

  proof
    cW
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    cN
    cfv
    #
    cA
    c.0
    cD
    co
    #
    cA
    c.0
    cE
    co
    #
    @1
    @3
    @4
    wceq
    @0
    cA
    cD
    cN
    cW
    cX
    c.0
    nmfval.n
    nmfval.x
    nmfval.z
    nmfval.d
    nmval
    adantl
    @2
    @5
    cA
    c.0
    cD
    cX
    cX
    cxp
    cres
    #
    co
    #
    @4
    cE
    @6
    cA
    c.0
    nmfval.e
    oveqi
    @1
    @1
    c.0
    cX
    wcel
    @7
    @4
    wceq
    @0
    @1
    id
    cX
    cW
    c.0
    nmfval.x
    nmfval.z
    grpidcl
    cA
    c.0
    cX
    cX
    cD
    ovres
    syl2anr
    syl5req
    eqtrd
end
