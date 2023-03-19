include "cric.mm"
include "wbr.mm"
include "crs.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "crg.mm"
include "wa.mm"
include "brric.mm"
include "n0.mm"
include "cvv.mm"
include "rimrcl.mm"
include "crh.mm"
include "ccnv.mm"
include "isrim0.mm"
include "cghm.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "eqid.mm"
include "isrhm.mm"
include "simplbi.mm"
include "adantr.mm"
include "syl6bi.mm"
include "mpcom.mm"
include "exlimiv.mm"
include "pm4.71ri.mm"
include "3bitri.mm"

theorem brric2
  let cR: class R
  let cS: class S
  let vf: setvar f

  disjoint R f
  disjoint S f
  assert |- ( R ~=r S <-> ( ( R e. Ring /\ S e. Ring ) /\ E. f f e. ( R RingIso S ) ) )

  proof
    cR
    cS
    cric
    wbr
    cR
    cS
    crs
    co
    #
    c0
    wne
    vf
    cv
    #
    @0
    wcel
    #
    vf
    wex
    #
    cR
    crg
    wcel
    cS
    crg
    wcel
    wa
    #
    @3
    wa
    cR
    cS
    brric
    vf
    @0
    n0
    @3
    @4
    @2
    @4
    vf
    cR
    cvv
    wcel
    cS
    cvv
    wcel
    wa
    #
    @2
    @4
    cR
    cS
    @1
    rimrcl
    @5
    @2
    @1
    cR
    cS
    crh
    co
    wcel
    #
    @1
    ccnv
    cS
    cR
    crh
    co
    wcel
    #
    wa
    @4
    cR
    cS
    @1
    cvv
    cvv
    isrim0
    @6
    @4
    @7
    @6
    @4
    @1
    cR
    cS
    cghm
    co
    wcel
    @1
    cR
    cmgp
    cfv
    #
    cS
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    wa
    cR
    cS
    @1
    @8
    @9
    @8
    eqid
    @9
    eqid
    isrhm
    simplbi
    adantr
    syl6bi
    mpcom
    exlimiv
    pm4.71ri
    3bitri
end
