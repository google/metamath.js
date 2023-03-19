include "wbr.mm"
include "wpss.mm"
include "wa.mm"
include "lcvpss.mm"
include "jca.mm"
include "wn.mm"
include "wcel.mm"
include "adantr.mm"
include "simpr.mm"
include "lcvnbtwn.mm"
include "ex.mm"
include "mt2d.mm"

theorem lcvntr
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cW: class W
  let cX: class X
  let vu: setvar u
  assume lcvnbtwn.s: |- S = ( LSubSp ` W )
  assume lcvnbtwn.c: |- C = ( <oL ` W )
  assume lcvnbtwn.w: |- ( ph -> W e. X )
  assume lcvnbtwn.r: |- ( ph -> R e. S )
  assume lcvnbtwn.t: |- ( ph -> T e. S )
  assume lcvnbtwn.u: |- ( ph -> U e. S )
  assume lcvnbtwn.d: |- ( ph -> R C T )
  assume lcvntr.p: |- ( ph -> T C U )


  assert |- ( ph -> -. R C U )

  proof
    wph
    cR
    cU
    cC
    wbr
    #
    cR
    cT
    wpss
    #
    cT
    cU
    wpss
    #
    wa
    #
    wph
    @1
    @2
    wph
    cC
    cS
    cR
    cT
    cW
    cX
    lcvnbtwn.s
    lcvnbtwn.c
    lcvnbtwn.w
    lcvnbtwn.r
    lcvnbtwn.t
    lcvnbtwn.d
    lcvpss
    wph
    cC
    cS
    cT
    cU
    cW
    cX
    lcvnbtwn.s
    lcvnbtwn.c
    lcvnbtwn.w
    lcvnbtwn.t
    lcvnbtwn.u
    lcvntr.p
    lcvpss
    jca
    wph
    @0
    @3
    wn
    wph
    @0
    wa
    cC
    cR
    cS
    cU
    cT
    cW
    cX
    lcvnbtwn.s
    lcvnbtwn.c
    wph
    cW
    cX
    wcel
    @0
    lcvnbtwn.w
    adantr
    wph
    cR
    cS
    wcel
    @0
    lcvnbtwn.r
    adantr
    wph
    cU
    cS
    wcel
    @0
    lcvnbtwn.u
    adantr
    wph
    cT
    cS
    wcel
    @0
    lcvnbtwn.t
    adantr
    wph
    @0
    simpr
    lcvnbtwn
    ex
    mt2d
end
