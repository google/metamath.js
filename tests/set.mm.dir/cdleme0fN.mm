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
include "simp3r.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "simp2r.mm"
include "nbrne2.mm"
include "syl2anc.mm"

theorem cdleme0fN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume cdleme0.l: |- .<_ = ( le ` K )
  assume cdleme0.j: |- .\/ = ( join ` K )
  assume cdleme0.m: |- ./\ = ( meet ` K )
  assume cdleme0.a: |- A = ( Atoms ` K )
  assume cdleme0.h: |- H = ( LHyp ` K )
  assume cdleme0.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme0c.3: |- V = ( ( P .\/ R ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ R e. A ) ) -> V =/= P )

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
    cR
    cA
    wcel
    #
    wa
    #
    w3a
    #
    cV
    cW
    c.le
    wbr
    @4
    cV
    cP
    wne
    @9
    cV
    cP
    cR
    c.or
    co
    #
    cW
    c.an
    co
    #
    cW
    c.le
    cdleme0c.3
    @9
    cK
    clat
    wcel
    #
    @10
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @13
    wcel
    #
    @11
    cW
    c.le
    wbr
    @9
    @0
    @12
    @0
    @1
    @5
    @8
    simp1l
    cK
    hllat
    syl
    #
    @9
    @12
    cP
    @13
    wcel
    #
    cR
    @13
    wcel
    #
    @14
    @16
    @9
    @3
    @17
    @2
    @3
    @4
    @8
    simp2l
    cA
    @13
    cP
    cK
    @13
    eqid
    #
    cdleme0.a
    atbase
    syl
    @9
    @7
    @18
    @2
    @5
    @6
    @7
    simp3r
    cA
    @13
    cR
    cK
    @19
    cdleme0.a
    atbase
    syl
    @13
    c.or
    cK
    cP
    cR
    @19
    cdleme0.j
    latjcl
    syl3anc
    @9
    @1
    @15
    @0
    @1
    @5
    @8
    simp1r
    @13
    cH
    cK
    cW
    @19
    cdleme0.h
    lhpbase
    syl
    @13
    cK
    c.le
    c.an
    @10
    cW
    @19
    cdleme0.l
    cdleme0.m
    latmle2
    syl3anc
    syl5eqbr
    @2
    @3
    @4
    @8
    simp2r
    cV
    cP
    cW
    c.le
    nbrne2
    syl2anc
end
