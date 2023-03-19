include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cv.mm"
include "wss.mm"
include "csubg.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "crn.mm"
include "wb.mm"
include "snssg.mm"
include "bicomd.mm"
include "adantl.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "cmre.mm"
include "wceq.mm"
include "subgacs.mm"
include "acsmred.mm"
include "snssi.mm"
include "mrcval.mm"
include "syl2an.mm"
include "cycsubg.mm"
include "3eqtr4d.mm"

theorem cycsubg2
  let vx: setvar x
  let cA: class A
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cK: class K
  let cX: class X
  let vy: setvar y
  assume cycsubg2.x: |- X = ( Base ` G )
  assume cycsubg2.t: |- .x. = ( .g ` G )
  assume cycsubg2.f: |- F = ( x e. ZZ |-> ( x .x. A ) )
  assume cycsubg2.k: |- K = ( mrCls ` ( SubGrp ` G ) )

  disjoint A x
  disjoint G x
  disjoint .x. x
  disjoint X x
  disjoint x y
  disjoint A y
  disjoint G y
  disjoint X y
  disjoint F y
  disjoint K y
  assert |- ( ( G e. Grp /\ A e. X ) -> ( K ` { A } ) = ran F )

  proof
    cG
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
    csn
    #
    vy
    cv
    #
    wss
    #
    vy
    cG
    csubg
    cfv
    #
    crab
    #
    cint
    #
    cA
    @4
    wcel
    #
    vy
    @6
    crab
    #
    cint
    @3
    cK
    cfv
    #
    cF
    crn
    @2
    @7
    @10
    @2
    @5
    @9
    vy
    @6
    @1
    @5
    @9
    wb
    @0
    @1
    @9
    @5
    cA
    @4
    cX
    snssg
    bicomd
    adantl
    rabbidv
    inteqd
    @0
    @6
    cX
    cmre
    cfv
    wcel
    @3
    cX
    wss
    @11
    @8
    wceq
    @1
    @0
    @6
    cX
    cX
    cG
    cycsubg2.x
    subgacs
    acsmred
    cA
    cX
    snssi
    @6
    @3
    cK
    cX
    vy
    cycsubg2.k
    mrcval
    syl2an
    vx
    cA
    c.x
    cF
    cG
    cX
    vy
    cycsubg2.x
    cycsubg2.t
    cycsubg2.f
    cycsubg
    3eqtr4d
end
