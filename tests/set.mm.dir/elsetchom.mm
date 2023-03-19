include "co.mm"
include "wcel.mm"
include "cmap.mm"
include "wf.mm"
include "setchom.mm"
include "eleq2d.mm"
include "elmapd.mm"
include "bitrd.mm"

theorem elsetchom
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cF: class F
  let cH: class H
  let cV: class V
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cZ: class Z
  assume setcbas.c: |- C = ( SetCat ` U )
  assume setcbas.u: |- ( ph -> U e. V )
  assume setchomfval.h: |- H = ( Hom ` C )
  assume setchom.x: |- ( ph -> X e. U )
  assume setchom.y: |- ( ph -> Y e. U )


  assert |- ( ph -> ( F e. ( X H Y ) <-> F : X --> Y ) )

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
    cY
    cX
    cmap
    co
    #
    wcel
    cX
    cY
    cF
    wf
    wph
    @0
    @1
    cF
    wph
    cC
    cU
    cH
    cV
    cX
    cY
    setcbas.c
    setcbas.u
    setchomfval.h
    setchom.x
    setchom.y
    setchom
    eleq2d
    wph
    cY
    cX
    cF
    cU
    cU
    setchom.y
    setchom.x
    elmapd
    bitrd
end
