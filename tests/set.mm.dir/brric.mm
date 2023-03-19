include "cric.mm"
include "crs.mm"
include "cvv.mm"
include "cxp.mm"
include "df-ric.mm"
include "cv.mm"
include "ccnv.mm"
include "crh.mm"
include "co.mm"
include "wcel.mm"
include "crab.mm"
include "wral.mm"
include "wfn.mm"
include "wa.mm"
include "ovex.mm"
include "rabexg.mm"
include "mp1i.mm"
include "rgen2a.mm"
include "df-rngiso.mm"
include "fnmpt2.mm"
include "ax-mp.mm"
include "brwitnlem.mm"

theorem brric
  let cR: class R
  let cS: class S
  let vh: setvar h
  let vr: setvar r
  let vs: setvar s


  assert |- ( R ~=r S <-> ( R RingIso S ) =/= (/) )

  proof
    cR
    cS
    cric
    crs
    cvv
    cvv
    cxp
    #
    df-ric
    vh
    cv
    ccnv
    vs
    cv
    #
    vr
    cv
    #
    crh
    co
    wcel
    #
    vh
    @2
    @1
    crh
    co
    #
    crab
    #
    cvv
    wcel
    #
    vs
    cvv
    wral
    vr
    cvv
    wral
    crs
    @0
    wfn
    @6
    vr
    vs
    cvv
    @4
    cvv
    wcel
    @6
    @2
    cvv
    wcel
    @1
    cvv
    wcel
    wa
    @2
    @1
    crh
    ovex
    @3
    vh
    @4
    cvv
    rabexg
    mp1i
    rgen2a
    vr
    vs
    cvv
    cvv
    @5
    crs
    cvv
    vh
    vs
    vr
    df-rngiso
    fnmpt2
    ax-mp
    brwitnlem
end
