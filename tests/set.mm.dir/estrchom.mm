include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "cvv.mm"
include "estrchomfval.mm"
include "wceq.mm"
include "wa.mm"
include "fveq2.mm"
include "oveqan12rd.mm"
include "oveq12i.mm"
include "syl6eqr.mm"
include "adantl.mm"
include "ovexd.mm"
include "ovmpt2d.mm"

theorem estrchom
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vz: setvar z
  assume estrcbas.c: |- C = ( ExtStrCat ` U )
  assume estrcbas.u: |- ( ph -> U e. V )
  assume estrchomfval.h: |- H = ( Hom ` C )
  assume estrchom.x: |- ( ph -> X e. U )
  assume estrchom.y: |- ( ph -> Y e. U )
  assume estrchom.a: |- A = ( Base ` X )
  assume estrchom.b: |- B = ( Base ` Y )


  assert |- ( ph -> ( X H Y ) = ( B ^m A ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cU
    cU
    vy
    cv
    #
    cbs
    cfv
    #
    vx
    cv
    #
    cbs
    cfv
    #
    cmap
    co
    #
    cB
    cA
    cmap
    co
    #
    cH
    cvv
    wph
    vx
    vy
    cC
    cU
    cH
    cV
    estrcbas.c
    estrcbas.u
    estrchomfval.h
    estrchomfval
    @2
    cX
    wceq
    #
    @0
    cY
    wceq
    #
    wa
    #
    @4
    @5
    wceq
    wph
    @8
    @4
    cY
    cbs
    cfv
    #
    cX
    cbs
    cfv
    #
    cmap
    co
    @5
    @7
    @6
    @1
    @9
    @3
    @10
    cmap
    @0
    cY
    cbs
    fveq2
    @2
    cX
    cbs
    fveq2
    oveqan12rd
    cB
    @9
    cA
    @10
    cmap
    estrchom.b
    estrchom.a
    oveq12i
    syl6eqr
    adantl
    estrchom.x
    estrchom.y
    wph
    cB
    cA
    cmap
    ovexd
    ovmpt2d
end
