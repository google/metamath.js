include "cfv.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "cv.mm"
include "cvv.mm"
include "ccid.mm"
include "cmpt.mm"
include "ccat.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "ringccatidALTV.mm"
include "syl.mm"
include "simprd.mm"
include "syl5eq.mm"
include "fveq2.mm"
include "adantl.mm"
include "reseq2d.mm"
include "fvex.mm"
include "resiexg.mm"
include "mp1i.mm"
include "fvmptd.mm"
include "reseq2i.mm"
include "syl6eqr.mm"

theorem ringcidALTV
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
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
  let vk: setvar k
  assume ringccatALTV.c: |- C = ( RingCatALTV ` U )
  assume ringcidALTV.b: |- B = ( Base ` C )
  assume ringcidALTV.o: |- .1. = ( Id ` C )
  assume ringcidALTV.u: |- ( ph -> U e. V )
  assume ringcidALTV.x: |- ( ph -> X e. B )
  assume ringcidALTV.s: |- S = ( Base ` X )


  assert |- ( ph -> ( .1. ` X ) = ( _I |` S ) )

  proof
    wph
    cX
    c.1
    cfv
    cid
    cX
    cbs
    cfv
    #
    cres
    #
    cid
    cS
    cres
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
    @1
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
    @4
    cmpt
    #
    ringcidALTV.o
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
    ringcidALTV.u
    vx
    cB
    cC
    cU
    cV
    ringccatALTV.c
    ringcidALTV.b
    ringccatidALTV
    syl
    simprd
    syl5eq
    wph
    @2
    cX
    wceq
    #
    wa
    @3
    @0
    cid
    @9
    @3
    @0
    wceq
    wph
    @2
    cX
    cbs
    fveq2
    adantl
    reseq2d
    ringcidALTV.x
    @0
    cvv
    wcel
    @1
    cvv
    wcel
    wph
    cX
    cbs
    fvex
    @0
    cvv
    resiexg
    mp1i
    fvmptd
    cS
    @0
    cid
    ringcidALTV.s
    reseq2i
    syl6eqr
end
