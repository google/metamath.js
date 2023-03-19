include "wbr.mm"
include "wpss.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wn.mm"
include "wss.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "lcvbr.mm"
include "iman.mm"
include "anass.mm"
include "dfpss2.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "xchbinx.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"
include "syl6bbr.mm"

theorem lcvbr2
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

  disjoint S s
  disjoint W s
  disjoint T s
  disjoint U s
  disjoint s t
  disjoint s u
  disjoint s w
  disjoint t u
  disjoint t w
  disjoint S t
  disjoint u w
  disjoint S u
  disjoint S w
  disjoint W t
  disjoint W u
  disjoint W w
  disjoint T t
  disjoint T u
  disjoint U t
  disjoint U u
  assert |- ( ph -> ( T C U <-> ( T C. U /\ A. s e. S ( ( T C. s /\ s C_ U ) -> s = U ) ) ) )

  proof
    wph
    cT
    cU
    cC
    wbr
    cT
    cU
    wpss
    #
    cT
    vs
    cv
    #
    wpss
    #
    @1
    cU
    wpss
    #
    wa
    #
    vs
    cS
    wrex
    wn
    #
    wa
    @0
    @2
    @1
    cU
    wss
    #
    wa
    #
    @1
    cU
    wceq
    #
    wi
    #
    vs
    cS
    wral
    #
    wa
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
    @10
    @5
    @0
    @10
    @4
    wn
    #
    vs
    cS
    wral
    @5
    @9
    @11
    vs
    cS
    @9
    @7
    @8
    wn
    #
    wa
    #
    @4
    @7
    @8
    iman
    @13
    @2
    @6
    @12
    wa
    #
    wa
    @4
    @2
    @6
    @12
    anass
    @3
    @14
    @2
    @1
    cU
    dfpss2
    anbi2i
    bitr4i
    xchbinx
    ralbii
    @4
    vs
    cS
    ralnex
    bitri
    anbi2i
    syl6bbr
end
