include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "w3a.mm"
include "wne.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr3l.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simpr1l.mm"
include "simpr2.mm"
include "simpr3r.mm"
include "latnlej1l.mm"
include "syl131anc.mm"
include "necomd.mm"
include "lhpat.mm"
include "syl112anc.mm"
include "syl5eqel.mm"

theorem cdleme3e
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume cdleme1.l: |- .<_ = ( le ` K )
  assume cdleme1.j: |- .\/ = ( join ` K )
  assume cdleme1.m: |- ./\ = ( meet ` K )
  assume cdleme1.a: |- A = ( Atoms ` K )
  assume cdleme1.h: |- H = ( LHyp ` K )
  assume cdleme1.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme1.f: |- F = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )
  assume cdleme3.3: |- V = ( ( P .\/ R ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ Q e. A /\ ( R e. A /\ -. R .<_ ( P .\/ Q ) ) ) ) -> V e. A )

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
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    wa
    #
    cV
    cP
    cR
    c.or
    co
    cW
    c.an
    co
    #
    cA
    cdleme3.3
    @11
    @2
    @5
    @7
    cP
    cR
    wne
    @12
    cA
    wcel
    @2
    @10
    simpl
    @2
    @5
    @6
    @9
    simpr1
    @7
    @8
    @5
    @6
    @2
    simpr3l
    #
    @11
    cR
    cP
    @11
    cK
    clat
    wcel
    #
    cR
    cK
    cbs
    cfv
    #
    wcel
    #
    cP
    @15
    wcel
    #
    cQ
    @15
    wcel
    #
    @8
    cR
    cP
    wne
    @0
    @14
    @1
    @10
    cK
    hllat
    ad2antrr
    @11
    @7
    @16
    @13
    cA
    @15
    cR
    cK
    @15
    eqid
    #
    cdleme1.a
    atbase
    syl
    @11
    @3
    @17
    @3
    @4
    @6
    @9
    @2
    simpr1l
    cA
    @15
    cP
    cK
    @19
    cdleme1.a
    atbase
    syl
    @11
    @6
    @18
    @2
    @5
    @6
    @9
    simpr2
    cA
    @15
    cQ
    cK
    @19
    cdleme1.a
    atbase
    syl
    @7
    @8
    @5
    @6
    @2
    simpr3r
    @15
    c.or
    cK
    c.le
    cR
    cP
    cQ
    @19
    cdleme1.l
    cdleme1.j
    latnlej1l
    syl131anc
    necomd
    cA
    cP
    cR
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme1.l
    cdleme1.j
    cdleme1.m
    cdleme1.a
    cdleme1.h
    lhpat
    syl112anc
    syl5eqel
end
