include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "oveq2i.mm"
include "cp1.mm"
include "cfv.mm"
include "cbs.mm"
include "wceq.mm"
include "simpll.mm"
include "simprrl.mm"
include "clat.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "atbase.mm"
include "ad2antrl.mm"
include "syl.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "latlej2.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "lhpjat2.mm"
include "adantrl.mm"
include "oveq2d.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "syl5eq.mm"

theorem cdleme0cq
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ ( Q e. A /\ -. Q .<_ W ) ) ) -> ( Q .\/ U ) = ( P .\/ Q ) )

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
    wa
    #
    cQ
    cU
    c.or
    co
    cQ
    cP
    cQ
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    @9
    cU
    @10
    cQ
    c.or
    cdleme0.u
    oveq2i
    @8
    @11
    @9
    cQ
    cW
    c.or
    co
    #
    c.an
    co
    #
    @9
    cK
    cp1
    cfv
    #
    c.an
    co
    #
    @9
    @8
    @0
    @4
    @9
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @16
    wcel
    #
    cQ
    @9
    c.le
    wbr
    #
    @11
    @13
    wceq
    @0
    @1
    @7
    simpll
    @2
    @3
    @4
    @5
    simprrl
    #
    @8
    cK
    clat
    wcel
    #
    cP
    @16
    wcel
    #
    cQ
    @16
    wcel
    #
    @17
    @0
    @21
    @1
    @7
    cK
    hllat
    ad2antrr
    #
    @3
    @22
    @2
    @6
    cA
    @16
    cP
    cK
    @16
    eqid
    #
    cdleme0.a
    atbase
    ad2antrl
    #
    @8
    @4
    @23
    @20
    cA
    @16
    cQ
    cK
    @25
    cdleme0.a
    atbase
    syl
    #
    @16
    c.or
    cK
    cP
    cQ
    @25
    cdleme0.j
    latjcl
    syl3anc
    #
    @1
    @18
    @0
    @7
    @16
    cH
    cK
    cW
    @25
    cdleme0.h
    lhpbase
    ad2antlr
    @8
    @21
    @22
    @23
    @19
    @24
    @26
    @27
    @16
    c.or
    cK
    c.le
    cP
    cQ
    @25
    cdleme0.l
    cdleme0.j
    latlej2
    syl3anc
    cA
    @16
    cQ
    c.or
    cK
    c.le
    c.an
    @9
    cW
    @25
    cdleme0.l
    cdleme0.j
    cdleme0.m
    cdleme0.a
    atmod3i1
    syl131anc
    @8
    @12
    @14
    @9
    c.an
    @2
    @6
    @12
    @14
    wceq
    @3
    cA
    cQ
    @14
    cH
    c.or
    cK
    c.le
    cW
    cdleme0.l
    cdleme0.j
    @14
    eqid
    #
    cdleme0.a
    cdleme0.h
    lhpjat2
    adantrl
    oveq2d
    @8
    cK
    col
    wcel
    #
    @17
    @15
    @9
    wceq
    @0
    @30
    @1
    @7
    cK
    hlol
    ad2antrr
    @28
    @16
    @14
    cK
    c.an
    @9
    @25
    cdleme0.m
    @29
    olm11
    syl2anc
    3eqtrd
    syl5eq
end
