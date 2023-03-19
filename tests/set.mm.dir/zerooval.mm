include "cv.mm"
include "cinito.mm"
include "cfv.mm"
include "ctermo.mm"
include "cin.mm"
include "ccat.mm"
include "czeroo.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-zeroo.mm"
include "a1i.mm"
include "fveq2.mm"
include "ineq12d.mm"
include "adantl.mm"
include "wcel.mm"
include "fvex.mm"
include "inex1.mm"
include "fvmptd.mm"

theorem zerooval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vh: setvar h
  assume initoval.c: |- ( ph -> C e. Cat )
  assume initoval.b: |- B = ( Base ` C )
  assume initoval.h: |- H = ( Hom ` C )


  assert |- ( ph -> ( ZeroO ` C ) = ( ( InitO ` C ) i^i ( TermO ` C ) ) )

  proof
    wph
    vc
    cC
    vc
    cv
    #
    cinito
    cfv
    #
    @0
    ctermo
    cfv
    #
    cin
    #
    cC
    cinito
    cfv
    #
    cC
    ctermo
    cfv
    #
    cin
    #
    ccat
    czeroo
    cvv
    czeroo
    vc
    ccat
    @3
    cmpt
    wceq
    wph
    vc
    df-zeroo
    a1i
    @0
    cC
    wceq
    #
    @3
    @6
    wceq
    wph
    @7
    @1
    @4
    @2
    @5
    @0
    cC
    cinito
    fveq2
    @0
    cC
    ctermo
    fveq2
    ineq12d
    adantl
    initoval.c
    @6
    cvv
    wcel
    wph
    @4
    @5
    cC
    cinito
    fvex
    inex1
    a1i
    fvmptd
end
