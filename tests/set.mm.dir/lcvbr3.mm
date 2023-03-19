include "wbr.mm"
include "wpss.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wn.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "lcvbr.mm"
include "iman.mm"
include "wne.mm"
include "df-pss.mm"
include "necom.mm"
include "anbi2i.mm"
include "bitri.mm"
include "anbi12i.mm"
include "an4.mm"
include "neanior.mm"
include "xchbinxr.mm"
include "ralbii.mm"
include "ralnex.mm"
include "syl6bbr.mm"

theorem lcvbr3
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
  assert |- ( ph -> ( T C U <-> ( T C. U /\ A. s e. S ( ( T C_ s /\ s C_ U ) -> ( s = T \/ s = U ) ) ) ) )

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
    cT
    @1
    wss
    #
    @1
    cU
    wss
    #
    wa
    #
    @1
    cT
    wceq
    @1
    cU
    wceq
    wo
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
    @11
    @5
    @0
    @11
    @4
    wn
    #
    vs
    cS
    wral
    @5
    @10
    @12
    vs
    cS
    @10
    @8
    @9
    wn
    #
    wa
    #
    @4
    @8
    @9
    iman
    @4
    @6
    @1
    cT
    wne
    #
    wa
    #
    @7
    @1
    cU
    wne
    #
    wa
    #
    wa
    #
    @14
    @2
    @16
    @3
    @18
    @2
    @6
    cT
    @1
    wne
    #
    wa
    @16
    cT
    @1
    df-pss
    @20
    @15
    @6
    cT
    @1
    necom
    anbi2i
    bitri
    @1
    cU
    df-pss
    anbi12i
    @19
    @8
    @15
    @17
    wa
    #
    wa
    @14
    @6
    @15
    @7
    @17
    an4
    @21
    @13
    @8
    @1
    cT
    @1
    cU
    neanior
    anbi2i
    bitri
    bitri
    xchbinxr
    ralbii
    @4
    vs
    cS
    ralnex
    bitri
    anbi2i
    syl6bbr
end
