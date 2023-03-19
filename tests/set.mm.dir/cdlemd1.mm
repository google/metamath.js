include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "co.mm"
include "w3a.mm"
include "wceq.mm"
include "simpll.mm"
include "simpr1l.mm"
include "simpr2l.mm"
include "simpr31.mm"
include "simpr32.mm"
include "simpr33.mm"
include "2llnma2.mm"
include "syl132anc.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "simpl.mm"
include "simpr1.mm"
include "cdlemc1.mm"
include "eqtr4d.mm"
include "simpr2.mm"
include "oveq12d.mm"
include "eqtr3d.mm"

theorem cdlemd1
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemd1.l: |- .<_ = ( le ` K )
  assume cdlemd1.j: |- .\/ = ( join ` K )
  assume cdlemd1.m: |- ./\ = ( meet ` K )
  assume cdlemd1.a: |- A = ( Atoms ` K )
  assume cdlemd1.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ P =/= Q /\ -. R .<_ ( P .\/ Q ) ) ) ) -> R = ( ( P .\/ ( ( P .\/ R ) ./\ W ) ) ./\ ( Q .\/ ( ( Q .\/ R ) ./\ W ) ) ) )

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
    cR
    cA
    wcel
    #
    cP
    cQ
    wne
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
    w3a
    #
    w3a
    #
    wa
    #
    cR
    cP
    c.or
    co
    #
    cR
    cQ
    c.or
    co
    #
    c.an
    co
    #
    cR
    cP
    cP
    cR
    c.or
    co
    #
    cW
    c.an
    co
    c.or
    co
    #
    cQ
    cQ
    cR
    c.or
    co
    #
    cW
    c.an
    co
    c.or
    co
    #
    c.an
    co
    @14
    @0
    @3
    @6
    @9
    @10
    @11
    @17
    cR
    wceq
    @0
    @1
    @13
    simpll
    @3
    @4
    @8
    @12
    @2
    simpr1l
    #
    @6
    @7
    @5
    @12
    @2
    simpr2l
    #
    @9
    @10
    @11
    @5
    @8
    @2
    simpr31
    #
    @9
    @10
    @11
    @5
    @8
    @2
    simpr32
    @9
    @10
    @11
    @5
    @8
    @2
    simpr33
    cA
    cP
    cQ
    cR
    c.or
    cK
    c.le
    c.an
    cdlemd1.l
    cdlemd1.j
    cdlemd1.m
    cdlemd1.a
    2llnma2
    syl132anc
    @14
    @15
    @19
    @16
    @21
    c.an
    @14
    @15
    @18
    @19
    @14
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
    @26
    wcel
    #
    @15
    @18
    wceq
    @0
    @25
    @1
    @13
    cK
    hllat
    ad2antrr
    #
    @14
    @9
    @27
    @24
    cA
    @26
    cR
    cK
    @26
    eqid
    #
    cdlemd1.a
    atbase
    syl
    #
    @14
    @3
    @28
    @22
    cA
    @26
    cP
    cK
    @30
    cdlemd1.a
    atbase
    syl
    @26
    c.or
    cK
    cR
    cP
    @30
    cdlemd1.j
    latjcom
    syl3anc
    @14
    @2
    @27
    @5
    @19
    @18
    wceq
    @2
    @13
    simpl
    #
    @31
    @2
    @5
    @8
    @12
    simpr1
    cA
    @26
    cP
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cR
    @30
    cdlemd1.l
    cdlemd1.j
    cdlemd1.m
    cdlemd1.a
    cdlemd1.h
    cdlemc1
    syl3anc
    eqtr4d
    @14
    @16
    @20
    @21
    @14
    @25
    @27
    cQ
    @26
    wcel
    #
    @16
    @20
    wceq
    @29
    @31
    @14
    @6
    @33
    @23
    cA
    @26
    cQ
    cK
    @30
    cdlemd1.a
    atbase
    syl
    @26
    c.or
    cK
    cR
    cQ
    @30
    cdlemd1.j
    latjcom
    syl3anc
    @14
    @2
    @27
    @8
    @21
    @20
    wceq
    @32
    @31
    @2
    @5
    @8
    @12
    simpr2
    cA
    @26
    cQ
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cR
    @30
    cdlemd1.l
    cdlemd1.j
    cdlemd1.m
    cdlemd1.a
    cdlemd1.h
    cdlemc1
    syl3anc
    eqtr4d
    oveq12d
    eqtr3d
end
