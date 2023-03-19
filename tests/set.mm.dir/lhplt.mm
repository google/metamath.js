include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cbs.mm"
include "cfv.mm"
include "cp1.mm"
include "ccvr.mm"
include "simpll.mm"
include "simprl.mm"
include "eqid.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "lhp1cvr.mm"
include "adantr.mm"
include "simprr.mm"
include "1cvratlt.mm"
include "syl32anc.mm"

theorem lhplt
  let cA: class A
  let cP: class P
  let c.lt: class .<
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume lhplt.l: |- .<_ = ( le ` K )
  assume lhplt.s: |- .< = ( lt ` K )
  assume lhplt.a: |- A = ( Atoms ` K )
  assume lhplt.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ P .<_ W ) ) -> P .< W )

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
    #
    wa
    #
    wa
    @0
    @3
    cW
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    cK
    cp1
    cfv
    #
    cK
    ccvr
    cfv
    #
    wbr
    #
    @4
    cP
    cW
    c.lt
    wbr
    @0
    @1
    @5
    simpll
    @2
    @3
    @4
    simprl
    @1
    @7
    @0
    @5
    @6
    cH
    cK
    cW
    @6
    eqid
    #
    lhplt.h
    lhpbase
    ad2antlr
    @2
    @10
    @5
    chlt
    @9
    @8
    cH
    cK
    cW
    @8
    eqid
    #
    @9
    eqid
    #
    lhplt.h
    lhp1cvr
    adantr
    @2
    @3
    @4
    simprr
    cA
    @6
    @9
    cP
    c.lt
    @8
    cK
    c.le
    cW
    @11
    lhplt.l
    lhplt.s
    @12
    @13
    lhplt.a
    1cvratlt
    syl32anc
end
