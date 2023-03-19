include "cfv.mm"
include "c2nd.mm"
include "cotp.mm"
include "idaval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "ot3rdg.mm"
include "ax-mp.mm"
include "syl6eq.mm"

theorem ida2
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


  assert |- ( ph -> ( 2nd ` ( I ` X ) ) = ( .1. ` X ) )

  proof
    wph
    cX
    cI
    cfv
    #
    c2nd
    cfv
    cX
    cX
    cX
    c.1
    cfv
    #
    cotp
    #
    c2nd
    cfv
    #
    @1
    wph
    @0
    @2
    c2nd
    wph
    cB
    cC
    c.1
    cI
    cX
    idafval.i
    idafval.b
    idafval.c
    idafval.1
    idaval.x
    idaval
    fveq2d
    @1
    cvv
    wcel
    @3
    @1
    wceq
    cX
    c.1
    fvex
    cX
    cX
    @1
    cvv
    ot3rdg
    ax-mp
    syl6eq
end
