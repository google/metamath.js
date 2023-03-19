include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "lhpmat.mm"
include "anassrs.mm"
include "wne.mm"
include "cal.mm"
include "hlatl.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "atn0.mm"
include "necomd.mm"
include "syl2anc.mm"
include "wb.mm"
include "neeq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "lhpbase.mm"
include "ad3antlr.mm"
include "latleeqm1.mm"
include "syl3anc.mm"
include "necon3bbid.mm"
include "impbida.mm"

theorem lhpmatb
  let cA: class A
  let cP: class P
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let c.0: class .0.
  assume lhpmat.l: |- .<_ = ( le ` K )
  assume lhpmat.m: |- ./\ = ( meet ` K )
  assume lhpmat.z: |- .0. = ( 0. ` K )
  assume lhpmat.a: |- A = ( Atoms ` K )
  assume lhpmat.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ P e. A ) -> ( -. P .<_ W <-> ( P ./\ W ) = .0. ) )

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
    cP
    cA
    wcel
    #
    wa
    #
    cP
    cW
    c.le
    wbr
    #
    wn
    #
    cP
    cW
    c.an
    co
    #
    c.0
    wceq
    #
    @2
    @3
    @6
    @8
    cA
    cP
    cH
    cK
    c.le
    c.an
    cW
    c.0
    lhpmat.l
    lhpmat.m
    lhpmat.z
    lhpmat.a
    lhpmat.h
    lhpmat
    anassrs
    @4
    @8
    wa
    #
    @6
    @7
    cP
    wne
    #
    @9
    @10
    c.0
    cP
    wne
    #
    @9
    cK
    cal
    wcel
    #
    @3
    @11
    @0
    @12
    @1
    @3
    @8
    cK
    hlatl
    ad3antrrr
    @2
    @3
    @8
    simplr
    #
    @12
    @3
    wa
    cP
    c.0
    cA
    cP
    cK
    c.0
    lhpmat.z
    lhpmat.a
    atn0
    necomd
    syl2anc
    @8
    @10
    @11
    wb
    @4
    @7
    c.0
    cP
    neeq1
    adantl
    mpbird
    @9
    @5
    @7
    cP
    @9
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @15
    wcel
    #
    @5
    @7
    cP
    wceq
    wb
    @0
    @14
    @1
    @3
    @8
    cK
    hllat
    ad3antrrr
    @9
    @3
    @16
    @13
    cA
    @15
    cP
    cK
    @15
    eqid
    #
    lhpmat.a
    atbase
    syl
    @1
    @17
    @0
    @3
    @8
    @15
    cH
    cK
    cW
    @18
    lhpmat.h
    lhpbase
    ad3antlr
    @15
    cK
    c.le
    c.an
    cP
    cW
    @18
    lhpmat.l
    lhpmat.m
    latleeqm1
    syl3anc
    necon3bbid
    mpbird
    impbida
end
