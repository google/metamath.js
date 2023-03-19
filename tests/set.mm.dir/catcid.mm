include "cfv.mm"
include "cidfu.mm"
include "cv.mm"
include "cvv.mm"
include "ccid.mm"
include "cmpt.mm"
include "ccat.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "catccatid.mm"
include "syl.mm"
include "simprd.mm"
include "syl5eq.mm"
include "simpr.mm"
include "fveq2d.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "syl6eqr.mm"

theorem catcid
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let c.1: class .1.
  let cI: class I
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume catccatid.c: |- C = ( CatCat ` U )
  assume catccatid.b: |- B = ( Base ` C )
  assume catcid.o: |- .1. = ( Id ` C )
  assume catcid.i: |- I = ( idFunc ` X )
  assume catcid.u: |- ( ph -> U e. V )
  assume catcid.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( .1. ` X ) = I )

  proof
    wph
    cX
    c.1
    cfv
    cX
    cidfu
    cfv
    #
    cI
    wph
    vx
    cX
    vx
    cv
    #
    cidfu
    cfv
    #
    @0
    cB
    c.1
    cvv
    wph
    c.1
    cC
    ccid
    cfv
    #
    vx
    cB
    @2
    cmpt
    #
    catcid.o
    wph
    cC
    ccat
    wcel
    #
    @3
    @4
    wceq
    #
    wph
    cU
    cV
    wcel
    @5
    @6
    wa
    catcid.u
    vx
    cB
    cC
    cU
    cV
    catccatid.c
    catccatid.b
    catccatid
    syl
    simprd
    syl5eq
    wph
    @1
    cX
    wceq
    #
    wa
    @1
    cX
    cidfu
    wph
    @7
    simpr
    fveq2d
    catcid.x
    wph
    cX
    cidfu
    fvexd
    fvmptd
    catcid.i
    syl6eqr
end
