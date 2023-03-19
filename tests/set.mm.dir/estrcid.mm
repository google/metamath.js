include "cid.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cres.mm"
include "cvv.mm"
include "ccid.mm"
include "cmpt.mm"
include "ccat.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "estrccatid.mm"
include "syl.mm"
include "simprd.mm"
include "syl5eq.mm"
include "fveq2.mm"
include "reseq2d.mm"
include "adantl.mm"
include "fvexd.mm"
include "resiexd.mm"
include "fvmptd.mm"

theorem estrcid
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
  assume estrccat.c: |- C = ( ExtStrCat ` U )
  assume estrcid.o: |- .1. = ( Id ` C )
  assume estrcid.u: |- ( ph -> U e. V )
  assume estrcid.x: |- ( ph -> X e. U )


  assert |- ( ph -> ( .1. ` X ) = ( _I |` ( Base ` X ) ) )

  proof
    wph
    vx
    cX
    cid
    vx
    cv
    #
    cbs
    cfv
    #
    cres
    #
    cid
    cX
    cbs
    cfv
    #
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
    @2
    cmpt
    #
    estrcid.o
    wph
    cC
    ccat
    wcel
    #
    @5
    @6
    wceq
    #
    wph
    cU
    cV
    wcel
    @7
    @8
    wa
    estrcid.u
    vx
    cC
    cU
    cV
    estrccat.c
    estrccatid
    syl
    simprd
    syl5eq
    @0
    cX
    wceq
    #
    @2
    @4
    wceq
    wph
    @9
    @1
    @3
    cid
    @0
    cX
    cbs
    fveq2
    reseq2d
    adantl
    estrcid.x
    wph
    @3
    cvv
    wph
    cX
    cbs
    fvexd
    resiexd
    fvmptd
end
