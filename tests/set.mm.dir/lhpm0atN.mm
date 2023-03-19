include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "ccvr.mm"
include "cfv.mm"
include "wbr.mm"
include "simpr3.mm"
include "cple.mm"
include "wn.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "eqid.mm"
include "latleeqm1.mm"
include "syl3anc.mm"
include "biimpa.mm"
include "simplr3.mm"
include "eqtr3d.mm"
include "ex.mm"
include "necon3ad.mm"
include "mpd.mm"
include "lhpmcvr.mm"
include "syl12anc.mm"
include "eqbrtrrd.mm"
include "simpll.mm"
include "isat2.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem lhpm0atN
  let cA: class A
  let cB: class B
  let cH: class H
  let cK: class K
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lhpm0at.b: |- B = ( Base ` K )
  assume lhpm0at.m: |- ./\ = ( meet ` K )
  assume lhpm0at.o: |- .0. = ( 0. ` K )
  assume lhpm0at.a: |- A = ( Atoms ` K )
  assume lhpm0at.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ X =/= .0. /\ ( X ./\ W ) = .0. ) ) -> X e. A )

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
    cX
    cB
    wcel
    #
    cX
    c.0
    wne
    #
    cX
    cW
    c.an
    co
    #
    c.0
    wceq
    #
    w3a
    #
    wa
    #
    cX
    cA
    wcel
    #
    c.0
    cX
    cK
    ccvr
    cfv
    #
    wbr
    #
    @8
    @5
    c.0
    cX
    @10
    @2
    @3
    @4
    @6
    simpr3
    @8
    @2
    @3
    cX
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    wn
    #
    @5
    cX
    @10
    wbr
    @2
    @7
    simpl
    @2
    @3
    @4
    @6
    simpr1
    #
    @8
    @4
    @14
    @2
    @3
    @4
    @6
    simpr2
    @8
    @13
    cX
    c.0
    @8
    @13
    cX
    c.0
    wceq
    @8
    @13
    wa
    @5
    cX
    c.0
    @8
    @13
    @5
    cX
    wceq
    #
    @8
    cK
    clat
    wcel
    #
    @3
    cW
    cB
    wcel
    #
    @13
    @16
    wb
    @0
    @17
    @1
    @7
    cK
    hllat
    ad2antrr
    @15
    @1
    @18
    @0
    @7
    cB
    cH
    cK
    cW
    lhpm0at.b
    lhpm0at.h
    lhpbase
    ad2antlr
    cB
    cK
    @12
    c.an
    cX
    cW
    lhpm0at.b
    @12
    eqid
    #
    lhpm0at.m
    latleeqm1
    syl3anc
    biimpa
    @3
    @4
    @6
    @2
    @13
    simplr3
    eqtr3d
    ex
    necon3ad
    mpd
    cB
    @10
    cH
    cK
    @12
    c.an
    cW
    cX
    lhpm0at.b
    @19
    lhpm0at.m
    @10
    eqid
    #
    lhpm0at.h
    lhpmcvr
    syl12anc
    eqbrtrrd
    @8
    @0
    @3
    @9
    @11
    wb
    @0
    @1
    @7
    simpll
    @15
    cA
    cB
    @10
    chlt
    cX
    cK
    c.0
    lhpm0at.b
    lhpm0at.o
    @20
    lhpm0at.a
    isat2
    syl2anc
    mpbird
end
