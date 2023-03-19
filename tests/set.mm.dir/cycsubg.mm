include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cv.mm"
include "csubg.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "wss.mm"
include "cab.mm"
include "wi.mm"
include "ssintab.mm"
include "cycsubgss.mm"
include "mpgbir.mm"
include "df-rab.mm"
include "inteqi.mm"
include "sseqtr4i.mm"
include "a1i.mm"
include "cycsubgcl.mm"
include "eleq2.mm"
include "elrab.mm"
include "sylibr.mm"
include "intss1.mm"
include "syl.mm"
include "eqssd.mm"

theorem cycsubg
  let vx: setvar x
  let cA: class A
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cX: class X
  let vs: setvar s
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let cS: class S
  assume cycsubg.x: |- X = ( Base ` G )
  assume cycsubg.t: |- .x. = ( .g ` G )
  assume cycsubg.f: |- F = ( x e. ZZ |-> ( x .x. A ) )

  disjoint s x
  disjoint A s
  disjoint A x
  disjoint G s
  disjoint G x
  disjoint .x. x
  disjoint X x
  disjoint F s
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint A m
  disjoint n s
  disjoint n x
  disjoint A n
  disjoint m u
  disjoint m v
  disjoint G m
  disjoint n u
  disjoint n v
  disjoint G n
  disjoint s u
  disjoint s v
  disjoint u v
  disjoint u x
  disjoint G u
  disjoint v x
  disjoint G v
  disjoint S x
  disjoint X m
  disjoint X n
  disjoint F m
  disjoint F n
  disjoint F u
  disjoint F v
  assert |- ( ( G e. Grp /\ A e. X ) -> ran F = |^| { s e. ( SubGrp ` G ) | A e. s } )

  proof
    cG
    cgrp
    wcel
    cA
    cX
    wcel
    wa
    #
    cF
    crn
    #
    cA
    vs
    cv
    #
    wcel
    #
    vs
    cG
    csubg
    cfv
    #
    crab
    #
    cint
    #
    @1
    @6
    wss
    @0
    @1
    @2
    @4
    wcel
    @3
    wa
    #
    vs
    cab
    #
    cint
    #
    @6
    @1
    @9
    wss
    @7
    @1
    @2
    wss
    wi
    vs
    @7
    vs
    @1
    ssintab
    vx
    cA
    @2
    c.x
    cF
    cG
    cX
    cycsubg.x
    cycsubg.t
    cycsubg.f
    cycsubgss
    mpgbir
    @5
    @8
    @3
    vs
    @4
    df-rab
    inteqi
    sseqtr4i
    a1i
    @0
    @1
    @5
    wcel
    #
    @6
    @1
    wss
    @0
    @1
    @4
    wcel
    cA
    @1
    wcel
    #
    wa
    @10
    vx
    cA
    c.x
    cF
    cG
    cX
    cycsubg.x
    cycsubg.t
    cycsubg.f
    cycsubgcl
    @3
    @11
    vs
    @1
    @4
    @2
    @1
    cA
    eleq2
    elrab
    sylibr
    @1
    @5
    intss1
    syl
    eqssd
end
