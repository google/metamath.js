include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wbr.mm"
include "simpll.mm"
include "hllat.mm"
include "syl.mm"
include "simprl.mm"
include "simprr.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "latmle1.mm"
include "syl5eqbr.mm"

theorem cdlemeulpq
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme0.l: |- .<_ = ( le ` K )
  assume cdleme0.j: |- .\/ = ( join ` K )
  assume cdleme0.m: |- ./\ = ( meet ` K )
  assume cdleme0.a: |- A = ( Atoms ` K )
  assume cdleme0.h: |- H = ( LHyp ` K )
  assume cdleme0.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ Q e. A ) ) -> U .<_ ( P .\/ Q ) )

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
    cQ
    cA
    wcel
    #
    wa
    #
    wa
    #
    cU
    cP
    cQ
    c.or
    co
    #
    cW
    c.an
    co
    #
    @7
    c.le
    cdleme0.u
    @6
    cK
    clat
    wcel
    #
    @7
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
    @8
    @7
    c.le
    wbr
    @6
    @0
    @9
    @0
    @1
    @5
    simpll
    #
    cK
    hllat
    syl
    @6
    @0
    @3
    @4
    @11
    @13
    @2
    @3
    @4
    simprl
    @2
    @3
    @4
    simprr
    cA
    @10
    c.or
    cK
    cP
    cQ
    @10
    eqid
    #
    cdleme0.j
    cdleme0.a
    hlatjcl
    syl3anc
    @1
    @12
    @0
    @5
    @10
    cH
    cK
    cW
    @14
    cdleme0.h
    lhpbase
    ad2antlr
    @10
    cK
    c.le
    c.an
    @7
    cW
    @14
    cdleme0.l
    cdleme0.m
    latmle1
    syl3anc
    syl5eqbr
end
