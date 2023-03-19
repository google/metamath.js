include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "atbase.mm"
include "ad2antrl.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "lhpjat1.mm"
include "eqtrd.mm"

theorem lhpjat2
  let cA: class A
  let cP: class P
  let c.1: class .1.
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume lhpjat.l: |- .<_ = ( le ` K )
  assume lhpjat.j: |- .\/ = ( join ` K )
  assume lhpjat.u: |- .1. = ( 1. ` K )
  assume lhpjat.a: |- A = ( Atoms ` K )
  assume lhpjat.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( P .\/ W ) = .1. )

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
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cP
    cW
    c.or
    co
    #
    cW
    cP
    c.or
    co
    #
    c.1
    @6
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
    @10
    wcel
    #
    @7
    @8
    wceq
    @0
    @9
    @1
    @5
    cK
    hllat
    ad2antrr
    @3
    @11
    @2
    @4
    cA
    @10
    cP
    cK
    @10
    eqid
    #
    lhpjat.a
    atbase
    ad2antrl
    @1
    @12
    @0
    @5
    @10
    cH
    cK
    cW
    @13
    lhpjat.h
    lhpbase
    ad2antlr
    @10
    c.or
    cK
    cP
    cW
    @13
    lhpjat.j
    latjcom
    syl3anc
    cA
    cP
    c.1
    cH
    c.or
    cK
    c.le
    cW
    lhpjat.l
    lhpjat.j
    lhpjat.u
    lhpjat.a
    lhpjat.h
    lhpjat1
    eqtrd
end
