include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "catm.mm"
include "cfv.mm"
include "wrex.mm"
include "eqid.mm"
include "lhpexlt.mm"
include "w3a.mm"
include "cbs.mm"
include "ccvr.mm"
include "simp1l.mm"
include "cops.mm"
include "hlop.mm"
include "op0cl.mm"
include "3syl.mm"
include "atbase.mm"
include "3ad2ant2.mm"
include "simp2.mm"
include "atcvr0.mm"
include "syl2anc.mm"
include "cvrlt.mm"
include "syl31anc.mm"
include "simp3.mm"
include "cpo.mm"
include "wi.mm"
include "hlpos.mm"
include "syl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "plttr.mm"
include "syl13anc.mm"
include "mp2and.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem lhp0lt
  let c.lt: class .<
  let cH: class H
  let cK: class K
  let cW: class W
  let c.0: class .0.
  let vp: setvar p
  assume lhp0lt.s: |- .< = ( lt ` K )
  assume lhp0lt.z: |- .0. = ( 0. ` K )
  assume lhp0lt.h: |- H = ( LHyp ` K )


  assert |- ( ( K e. HL /\ W e. H ) -> .0. .< W )

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
    vp
    cv
    #
    cW
    c.lt
    wbr
    #
    vp
    cK
    catm
    cfv
    #
    wrex
    c.0
    cW
    c.lt
    wbr
    #
    @5
    c.lt
    cH
    cK
    cW
    vp
    lhp0lt.s
    @5
    eqid
    #
    lhp0lt.h
    lhpexlt
    @2
    @4
    @6
    vp
    @5
    @2
    @3
    @5
    wcel
    #
    @4
    w3a
    #
    c.0
    @3
    c.lt
    wbr
    #
    @4
    @6
    @9
    @0
    c.0
    cK
    cbs
    cfv
    #
    wcel
    #
    @3
    @11
    wcel
    #
    c.0
    @3
    cK
    ccvr
    cfv
    #
    wbr
    #
    @10
    @0
    @1
    @8
    @4
    simp1l
    #
    @9
    @0
    cK
    cops
    wcel
    @12
    @16
    cK
    hlop
    @11
    cK
    c.0
    @11
    eqid
    #
    lhp0lt.z
    op0cl
    3syl
    #
    @8
    @2
    @13
    @4
    @5
    @11
    @3
    cK
    @17
    @7
    atbase
    3ad2ant2
    #
    @9
    @0
    @8
    @15
    @16
    @2
    @8
    @4
    simp2
    @5
    @14
    chlt
    @3
    cK
    c.0
    lhp0lt.z
    @14
    eqid
    #
    @7
    atcvr0
    syl2anc
    chlt
    @11
    @14
    c.lt
    cK
    c.0
    @3
    @17
    lhp0lt.s
    @20
    cvrlt
    syl31anc
    @2
    @8
    @4
    simp3
    @9
    cK
    cpo
    wcel
    #
    @12
    @13
    cW
    @11
    wcel
    #
    @10
    @4
    wa
    @6
    wi
    @9
    @0
    @21
    @16
    cK
    hlpos
    syl
    @18
    @19
    @9
    @1
    @22
    @0
    @1
    @8
    @4
    simp1r
    @11
    cH
    cK
    cW
    @17
    lhp0lt.h
    lhpbase
    syl
    @11
    c.lt
    cK
    c.0
    @3
    cW
    @17
    lhp0lt.s
    plttr
    syl13anc
    mp2and
    rexlimdv3a
    mpd
end
