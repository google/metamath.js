include "cid.mm"
include "cv.mm"
include "cres.mm"
include "cvv.mm"
include "ccid.mm"
include "cfv.mm"
include "cmpt.mm"
include "ccat.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "setccatid.mm"
include "syl.mm"
include "simprd.mm"
include "syl5eq.mm"
include "simpr.mm"
include "reseq2d.mm"
include "resiexg.mm"
include "fvmptd.mm"

theorem setcid
  let wph: wff ph
  let cC: class C
  let cU: class U
  let c.1: class .1.
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume setccat.c: |- C = ( SetCat ` U )
  assume setcid.o: |- .1. = ( Id ` C )
  assume setcid.u: |- ( ph -> U e. V )
  assume setcid.x: |- ( ph -> X e. U )


  assert |- ( ph -> ( .1. ` X ) = ( _I |` X ) )

  proof
    wph
    vx
    cX
    cid
    vx
    cv
    #
    cres
    #
    cid
    cX
    cres
    #
    cU
    c.1
    cvv
    wph
    c.1
    cC
    ccid
    cfv
    #
    vx
    cU
    @1
    cmpt
    #
    setcid.o
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
    setcid.u
    vx
    cC
    cU
    cV
    setccat.c
    setccatid
    syl
    simprd
    syl5eq
    wph
    @0
    cX
    wceq
    #
    wa
    @0
    cX
    cid
    wph
    @7
    simpr
    reseq2d
    setcid.x
    wph
    cX
    cU
    wcel
    @2
    cvv
    wcel
    setcid.x
    cX
    cU
    resiexg
    syl
    fvmptd
end
