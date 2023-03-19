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
include "simprll.mm"
include "clat.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simprr.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "hlatlej1.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "lhpjat2.mm"
include "adantrr.mm"
include "oveq2d.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "syl5eq.mm"

theorem cdleme0cp
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ Q e. A ) ) -> ( P .\/ U ) = ( P .\/ Q ) )

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
    wa
    #
    wa
    #
    cP
    cU
    c.or
    co
    cP
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
    cP
    c.or
    cdleme0.u
    oveq2i
    @8
    @11
    @9
    cP
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
    @3
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
    cP
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
    #
    @2
    @3
    @4
    @6
    simprll
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
    @22
    @1
    @7
    cK
    hllat
    ad2antrr
    @8
    @3
    @23
    @21
    cA
    @16
    cP
    cK
    @16
    eqid
    #
    cdleme0.a
    atbase
    syl
    @8
    @6
    @24
    @2
    @5
    @6
    simprr
    #
    cA
    @16
    cQ
    cK
    @25
    cdleme0.a
    atbase
    syl
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
    @0
    @3
    @6
    @19
    @20
    @21
    @26
    cA
    cP
    cQ
    c.or
    cK
    c.le
    cdleme0.l
    cdleme0.j
    cdleme0.a
    hlatlej1
    syl3anc
    cA
    @16
    cP
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
    @5
    @12
    @14
    wceq
    @6
    cA
    cP
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
    adantrr
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
    @29
    @1
    @7
    cK
    hlol
    ad2antrr
    @27
    @16
    @14
    cK
    c.an
    @9
    @25
    cdleme0.m
    @28
    olm11
    syl2anc
    3eqtrd
    syl5eq
end
