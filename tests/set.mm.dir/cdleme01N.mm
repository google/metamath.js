include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "co.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2ll.mm"
include "simp2rl.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "simp2lr.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "simp2rr.mm"
include "simp1.mm"
include "cdlemeulpq.mm"
include "syl12anc.mm"
include "3jca.mm"
include "jca.mm"

theorem cdleme01N
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ P =/= Q ) -> ( ( U =/= P /\ U =/= Q /\ U .<_ ( P .\/ Q ) ) /\ U .<_ W ) )

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
    cQ
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
    cQ
    wne
    #
    w3a
    #
    cU
    cP
    wne
    #
    cU
    cQ
    wne
    #
    cU
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    cU
    cW
    c.le
    wbr
    #
    @11
    @12
    @13
    @15
    @11
    @16
    @4
    @12
    @11
    cU
    @14
    cW
    c.an
    co
    #
    cW
    c.le
    cdleme0.u
    @11
    cK
    clat
    wcel
    #
    @14
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @19
    wcel
    #
    @17
    cW
    c.le
    wbr
    @11
    @0
    @18
    @0
    @1
    @9
    @10
    simp1l
    #
    cK
    hllat
    syl
    @11
    @0
    @3
    @6
    @20
    @22
    @3
    @4
    @8
    @2
    @10
    simp2ll
    #
    @6
    @7
    @5
    @2
    @10
    simp2rl
    #
    cA
    @19
    c.or
    cK
    cP
    cQ
    @19
    eqid
    #
    cdleme0.j
    cdleme0.a
    hlatjcl
    syl3anc
    @11
    @1
    @21
    @0
    @1
    @9
    @10
    simp1r
    @19
    cH
    cK
    cW
    @25
    cdleme0.h
    lhpbase
    syl
    @19
    cK
    c.le
    c.an
    @14
    cW
    @25
    cdleme0.l
    cdleme0.m
    latmle2
    syl3anc
    syl5eqbr
    #
    @3
    @4
    @8
    @2
    @10
    simp2lr
    cU
    cP
    cW
    c.le
    nbrne2
    syl2anc
    @11
    @16
    @7
    @13
    @26
    @6
    @7
    @5
    @2
    @10
    simp2rr
    cU
    cQ
    cW
    c.le
    nbrne2
    syl2anc
    @11
    @2
    @3
    @6
    @15
    @2
    @9
    @10
    simp1
    @23
    @24
    cA
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme0.l
    cdleme0.j
    cdleme0.m
    cdleme0.a
    cdleme0.h
    cdleme0.u
    cdlemeulpq
    syl12anc
    3jca
    @26
    jca
end
