include "cv.mm"
include "cfv.mm"
include "cotp.mm"
include "cvv.mm"
include "idafval.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "oteq123d.mm"
include "wcel.mm"
include "otex.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem idaval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.1: class .1.
  let cI: class I
  let cX: class X
  let vc: setvar c
  let vx: setvar x
  let cA: class A
  assume idafval.i: |- I = ( IdA ` C )
  assume idafval.b: |- B = ( Base ` C )
  assume idafval.c: |- ( ph -> C e. Cat )
  assume idafval.1: |- .1. = ( Id ` C )
  assume idaval.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( I ` X ) = <. X , X , ( .1. ` X ) >. )

  proof
    wph
    vx
    cX
    vx
    cv
    #
    @0
    @0
    c.1
    cfv
    #
    cotp
    cX
    cX
    cX
    c.1
    cfv
    #
    cotp
    #
    cB
    cI
    cvv
    wph
    vx
    cB
    cC
    c.1
    cI
    idafval.i
    idafval.b
    idafval.c
    idafval.1
    idafval
    wph
    @0
    cX
    wceq
    #
    wa
    #
    @0
    cX
    @0
    cX
    @1
    @2
    wph
    @4
    simpr
    #
    @6
    @5
    @0
    cX
    c.1
    @6
    fveq2d
    oteq123d
    idaval.x
    @3
    cvv
    wcel
    wph
    cX
    cX
    @2
    otex
    a1i
    fvmptd
end
