include "co.mm"
include "wcel.mm"
include "cmap.mm"
include "wf.mm"
include "estrchom.mm"
include "eleq2d.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "elmapg.mm"
include "syl2anc.mm"
include "bitrd.mm"

theorem elestrchom
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
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


  assert |- ( ph -> ( F e. ( X H Y ) <-> F : A --> B ) )

  proof
    wph
    cF
    cX
    cY
    cH
    co
    #
    wcel
    cF
    cB
    cA
    cmap
    co
    #
    wcel
    #
    cA
    cB
    cF
    wf
    #
    wph
    @0
    @1
    cF
    wph
    cA
    cB
    cC
    cU
    cH
    cV
    cX
    cY
    estrcbas.c
    estrcbas.u
    estrchomfval.h
    estrchom.x
    estrchom.y
    estrchom.a
    estrchom.b
    estrchom
    eleq2d
    wph
    cB
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    @2
    @3
    wb
    @4
    wph
    cB
    cY
    cbs
    cfv
    cvv
    estrchom.b
    cY
    cbs
    fvex
    eqeltri
    a1i
    @5
    wph
    cA
    cX
    cbs
    cfv
    cvv
    estrchom.a
    cX
    cbs
    fvex
    eqeltri
    a1i
    cB
    cA
    cF
    cvv
    cvv
    elmapg
    syl2anc
    bitrd
end
