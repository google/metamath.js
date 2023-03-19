include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cplt.mm"
include "cfv.mm"
include "wbr.mm"
include "wne.mm"
include "eqid.mm"
include "lhp0lt.mm"
include "cbs.mm"
include "wi.mm"
include "simpl.mm"
include "cops.mm"
include "hlop.mm"
include "op0cl.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "pltne.mm"
include "syl3anc.mm"
include "mpd.mm"
include "necomd.mm"

theorem lhpn0
  let cH: class H
  let cK: class K
  let cW: class W
  let c.0: class .0.
  assume lhpne0.z: |- .0. = ( 0. ` K )
  assume lhpne0.h: |- H = ( LHyp ` K )


  assert |- ( ( K e. HL /\ W e. H ) -> W =/= .0. )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    c.0
    cW
    @2
    c.0
    cW
    cK
    cplt
    cfv
    #
    wbr
    #
    c.0
    cW
    wne
    #
    @3
    cH
    cK
    cW
    c.0
    @3
    eqid
    #
    lhpne0.z
    lhpne0.h
    lhp0lt
    @2
    @0
    c.0
    cK
    cbs
    cfv
    #
    wcel
    #
    @1
    @4
    @5
    wi
    @0
    @1
    simpl
    @0
    @8
    @1
    @0
    cK
    cops
    wcel
    @8
    cK
    hlop
    @7
    cK
    c.0
    @7
    eqid
    lhpne0.z
    op0cl
    syl
    adantr
    @0
    @1
    simpr
    chlt
    @7
    cH
    @3
    cK
    c.0
    cW
    @6
    pltne
    syl3anc
    mpd
    necomd
end
