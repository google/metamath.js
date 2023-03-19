include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "co.mm"
include "wne.mm"
include "wceq.mm"
include "oveq1.mm"
include "neeq1d.mm"
include "cal.mm"
include "catm.mm"
include "cfv.mm"
include "simpl1.mm"
include "hlatl.mm"
include "syl.mm"
include "simpl2.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "simpr.mm"
include "eqid.mm"
include "2llnm2N.mm"
include "syl113anc.mm"
include "atn0.mm"
include "syl2anc.mm"
include "clat.mm"
include "cbs.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp22.mm"
include "llnbase.mm"
include "latmidm.mm"
include "simp1.mm"
include "llnn0.mm"
include "eqnetrd.mm"
include "pm2.61ne.mm"

theorem 2llnm3N
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume 2llnm3.l: |- .<_ = ( le ` K )
  assume 2llnm3.m: |- ./\ = ( meet ` K )
  assume 2llnm3.z: |- .0. = ( 0. ` K )
  assume 2llnm3.n: |- N = ( LLines ` K )
  assume 2llnm3.p: |- P = ( LPlanes ` K )


  assert |- ( ( K e. HL /\ ( X e. N /\ Y e. N /\ W e. P ) /\ ( X .<_ W /\ Y .<_ W ) ) -> ( X ./\ Y ) =/= .0. )

  proof
    cK
    chlt
    wcel
    #
    cX
    cN
    wcel
    #
    cY
    cN
    wcel
    #
    cW
    cP
    wcel
    #
    w3a
    #
    cX
    cW
    c.le
    wbr
    #
    cY
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cX
    cY
    c.an
    co
    #
    c.0
    wne
    #
    cY
    cY
    c.an
    co
    #
    c.0
    wne
    cX
    cY
    cX
    cY
    wceq
    @9
    @11
    c.0
    cX
    cY
    cY
    c.an
    oveq1
    neeq1d
    @8
    cX
    cY
    wne
    #
    wa
    #
    cK
    cal
    wcel
    #
    @9
    cK
    catm
    cfv
    #
    wcel
    #
    @10
    @13
    @0
    @14
    @0
    @4
    @7
    @12
    simpl1
    #
    cK
    hlatl
    syl
    @13
    @0
    @4
    @5
    @6
    @12
    @16
    @17
    @0
    @4
    @7
    @12
    simpl2
    @5
    @6
    @0
    @4
    @12
    simpl3l
    @5
    @6
    @0
    @4
    @12
    simpl3r
    @8
    @12
    simpr
    @15
    cP
    cK
    c.le
    c.an
    cN
    cW
    cX
    cY
    2llnm3.l
    2llnm3.m
    @15
    eqid
    #
    2llnm3.n
    2llnm3.p
    2llnm2N
    syl113anc
    @15
    @9
    cK
    c.0
    2llnm3.z
    @18
    atn0
    syl2anc
    @8
    @11
    cY
    c.0
    @8
    cK
    clat
    wcel
    #
    cY
    cK
    cbs
    cfv
    #
    wcel
    #
    @11
    cY
    wceq
    @0
    @4
    @19
    @7
    cK
    hllat
    3ad2ant1
    @8
    @2
    @21
    @0
    @1
    @2
    @3
    @7
    simp22
    #
    @20
    cK
    cN
    cY
    @20
    eqid
    #
    2llnm3.n
    llnbase
    syl
    @20
    cK
    c.an
    cY
    @23
    2llnm3.m
    latmidm
    syl2anc
    @8
    @0
    @2
    cY
    c.0
    wne
    @0
    @4
    @7
    simp1
    @22
    cK
    cN
    cY
    c.0
    2llnm3.z
    2llnm3.n
    llnn0
    syl2anc
    eqnetrd
    pm2.61ne
end
