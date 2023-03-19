include "wss.mm"
include "wpss.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "wi.mm"
include "lcvnbtwn.mm"
include "iman.mm"
include "eqcom.mm"
include "imbi2i.mm"
include "dfpss2.mm"
include "anbi1i.mm"
include "an32.mm"
include "bitri.mm"
include "notbii.mm"
include "3bitr4ri.mm"
include "sylib.mm"
include "mp2and.mm"

theorem lcvnbtwn3
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
  assume lcvnbtwn3.p: |- ( ph -> R C_ U )
  assume lcvnbtwn3.q: |- ( ph -> U C. T )


  assert |- ( ph -> U = R )

  proof
    wph
    cR
    cU
    wss
    #
    cU
    cT
    wpss
    #
    cU
    cR
    wceq
    #
    lcvnbtwn3.p
    lcvnbtwn3.q
    wph
    cR
    cU
    wpss
    #
    @1
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
    @6
    cR
    cU
    wceq
    #
    wi
    @6
    @8
    wn
    #
    wa
    #
    wn
    @7
    @5
    @6
    @8
    iman
    @2
    @8
    @6
    cU
    cR
    eqcom
    imbi2i
    @4
    @10
    @4
    @0
    @9
    wa
    #
    @1
    wa
    @10
    @3
    @11
    @1
    cR
    cU
    dfpss2
    anbi1i
    @0
    @9
    @1
    an32
    bitri
    notbii
    3bitr4ri
    sylib
    mp2and
end
