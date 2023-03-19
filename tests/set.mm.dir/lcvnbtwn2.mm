include "wpss.mm"
include "wss.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "wi.mm"
include "lcvnbtwn.mm"
include "iman.mm"
include "anass.mm"
include "dfpss2.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "notbii.mm"
include "bitr2i.mm"
include "sylib.mm"
include "mp2and.mm"

theorem lcvnbtwn2
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
  assume lcvnbtwn2.p: |- ( ph -> R C. U )
  assume lcvnbtwn2.q: |- ( ph -> U C_ T )


  assert |- ( ph -> U = T )

  proof
    wph
    cR
    cU
    wpss
    #
    cU
    cT
    wss
    #
    cU
    cT
    wceq
    #
    lcvnbtwn2.p
    lcvnbtwn2.q
    wph
    @0
    cU
    cT
    wpss
    #
    wa
    #
    wn
    #
    @0
    @1
    wa
    #
    @2
    wi
    #
    wph
    cC
    cR
    cS
    cT
    cU
    cW
    cX
    lcvnbtwn.s
    lcvnbtwn.c
    lcvnbtwn.w
    lcvnbtwn.r
    lcvnbtwn.t
    lcvnbtwn.u
    lcvnbtwn.d
    lcvnbtwn
    @7
    @6
    @2
    wn
    #
    wa
    #
    wn
    @5
    @6
    @2
    iman
    @9
    @4
    @9
    @0
    @1
    @8
    wa
    #
    wa
    @4
    @0
    @1
    @8
    anass
    @3
    @10
    @0
    cU
    cT
    dfpss2
    anbi2i
    bitr4i
    notbii
    bitr2i
    sylib
    mp2and
end
