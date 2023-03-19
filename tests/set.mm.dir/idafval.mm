include "cida.mm"
include "cfv.mm"
include "cv.mm"
include "cotp.mm"
include "cmpt.mm"
include "ccat.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "ccid.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "oteq3d.mm"
include "mpteq12dv.mm"
include "df-ida.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem idafval
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let c.1: class .1.
  let cI: class I
  let vc: setvar c
  let cA: class A
  let cX: class X
  assume idafval.i: |- I = ( IdA ` C )
  assume idafval.b: |- B = ( Base ` C )
  assume idafval.c: |- ( ph -> C e. Cat )
  assume idafval.1: |- .1. = ( Id ` C )

  disjoint .1. x
  disjoint B x
  disjoint C x
  disjoint I x
  disjoint ph x
  disjoint c x
  disjoint .1. c
  disjoint A x
  disjoint B c
  disjoint C c
  disjoint X x
  assert |- ( ph -> I = ( x e. B |-> <. x , x , ( .1. ` x ) >. ) )

  proof
    wph
    cI
    cC
    cida
    cfv
    #
    vx
    cB
    vx
    cv
    #
    @1
    @1
    c.1
    cfv
    #
    cotp
    #
    cmpt
    #
    idafval.i
    wph
    cC
    ccat
    wcel
    @0
    @4
    wceq
    idafval.c
    vc
    cC
    vx
    vc
    cv
    #
    cbs
    cfv
    #
    @1
    @1
    @1
    @5
    ccid
    cfv
    #
    cfv
    #
    cotp
    #
    cmpt
    @4
    ccat
    cida
    @5
    cC
    wceq
    #
    vx
    @6
    @9
    cB
    @3
    @10
    @6
    cC
    cbs
    cfv
    #
    cB
    @5
    cC
    cbs
    fveq2
    idafval.b
    syl6eqr
    @10
    @8
    @2
    @1
    @1
    @10
    @1
    @7
    c.1
    @10
    @7
    cC
    ccid
    cfv
    c.1
    @5
    cC
    ccid
    fveq2
    idafval.1
    syl6eqr
    fveq1d
    oteq3d
    mpteq12dv
    vx
    vc
    df-ida
    vx
    cB
    @3
    cB
    @11
    cvv
    idafval.b
    cC
    cbs
    fvex
    eqeltri
    mptex
    fvmpt
    syl
    syl5eq
end
