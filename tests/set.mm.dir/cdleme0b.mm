include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "eqid.mm"
include "atbase.mm"
include "3ad2ant3.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "simp2r.mm"
include "nbrne2.mm"
include "syl2anc.mm"

theorem cdleme0b
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ Q e. A ) -> U =/= P )

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
    cQ
    cA
    wcel
    #
    w3a
    #
    cU
    cW
    c.le
    wbr
    @4
    cU
    cP
    wne
    @7
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
    cW
    c.le
    cdleme0.u
    @7
    cK
    clat
    wcel
    #
    @8
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @11
    wcel
    #
    @9
    cW
    c.le
    wbr
    @7
    @0
    @10
    @0
    @1
    @5
    @6
    simp1l
    cK
    hllat
    syl
    #
    @7
    @10
    cP
    @11
    wcel
    #
    cQ
    @11
    wcel
    #
    @12
    @14
    @7
    @3
    @15
    @2
    @3
    @4
    @6
    simp2l
    cA
    @11
    cP
    cK
    @11
    eqid
    #
    cdleme0.a
    atbase
    syl
    @6
    @2
    @16
    @5
    cA
    @11
    cQ
    cK
    @17
    cdleme0.a
    atbase
    3ad2ant3
    @11
    c.or
    cK
    cP
    cQ
    @17
    cdleme0.j
    latjcl
    syl3anc
    @7
    @1
    @13
    @0
    @1
    @5
    @6
    simp1r
    @11
    cH
    cK
    cW
    @17
    cdleme0.h
    lhpbase
    syl
    @11
    cK
    c.le
    c.an
    @8
    cW
    @17
    cdleme0.l
    cdleme0.m
    latmle2
    syl3anc
    syl5eqbr
    @2
    @3
    @4
    @6
    simp2r
    cU
    cP
    cW
    c.le
    nbrne2
    syl2anc
end
