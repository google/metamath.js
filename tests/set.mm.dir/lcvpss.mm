include "wpss.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wn.mm"
include "wbr.mm"
include "lcvbr.mm"
include "mpbid.mm"
include "simpld.mm"

theorem lcvpss
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cT: class T
  let cU: class U
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  assume lcvfbr.s: |- S = ( LSubSp ` W )
  assume lcvfbr.c: |- C = ( <oL ` W )
  assume lcvfbr.w: |- ( ph -> W e. X )
  assume lcvfbr.t: |- ( ph -> T e. S )
  assume lcvfbr.u: |- ( ph -> U e. S )
  assume lcvpss.d: |- ( ph -> T C U )


  assert |- ( ph -> T C. U )

  proof
    wph
    cT
    cU
    wpss
    #
    cT
    vs
    cv
    #
    wpss
    @1
    cU
    wpss
    wa
    vs
    cS
    wrex
    wn
    #
    wph
    cT
    cU
    cC
    wbr
    @0
    @2
    wa
    lcvpss.d
    wph
    cC
    cS
    cT
    cU
    cW
    cX
    vs
    lcvfbr.s
    lcvfbr.c
    lcvfbr.w
    lcvfbr.t
    lcvfbr.u
    lcvbr
    mpbid
    simpld
end
