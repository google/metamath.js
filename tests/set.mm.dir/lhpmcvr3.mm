include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cp1.mm"
include "cfv.mm"
include "simpl1l.mm"
include "simpl3l.mm"
include "simpl2l.mm"
include "simpl1r.mm"
include "lhpbase.mm"
include "syl.mm"
include "simpr.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "simpl1.mm"
include "simpl3.mm"
include "eqid.mm"
include "lhpjat2.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "3eqtrd.mm"
include "clat.mm"
include "hllat.mm"
include "atbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latlej1.mm"
include "breqtrd.mm"
include "impbida.mm"

theorem lhpmcvr3
  let cA: class A
  let cB: class B
  let cP: class P
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let vp: setvar p
  assume lhpmcvr2.b: |- B = ( Base ` K )
  assume lhpmcvr2.l: |- .<_ = ( le ` K )
  assume lhpmcvr2.j: |- .\/ = ( join ` K )
  assume lhpmcvr2.m: |- ./\ = ( meet ` K )
  assume lhpmcvr2.a: |- A = ( Atoms ` K )
  assume lhpmcvr2.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( P .<_ X <-> ( P .\/ ( X ./\ W ) ) = X ) )

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
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    wn
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
    w3a
    #
    cP
    cX
    c.le
    wbr
    #
    cP
    cX
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    wceq
    #
    @9
    @10
    wa
    #
    @12
    cX
    cP
    cW
    c.or
    co
    #
    c.an
    co
    #
    cX
    cK
    cp1
    cfv
    #
    c.an
    co
    #
    cX
    @14
    @0
    @6
    @3
    cW
    cB
    wcel
    #
    @10
    @12
    @16
    wceq
    @0
    @1
    @5
    @8
    @10
    simpl1l
    #
    @6
    @7
    @2
    @5
    @10
    simpl3l
    @3
    @4
    @2
    @8
    @10
    simpl2l
    #
    @14
    @1
    @19
    @0
    @1
    @5
    @8
    @10
    simpl1r
    cB
    cH
    cK
    cW
    lhpmcvr2.b
    lhpmcvr2.h
    lhpbase
    #
    syl
    @9
    @10
    simpr
    cA
    cB
    cP
    c.or
    cK
    c.le
    c.an
    cX
    cW
    lhpmcvr2.b
    lhpmcvr2.l
    lhpmcvr2.j
    lhpmcvr2.m
    lhpmcvr2.a
    atmod3i1
    syl131anc
    @14
    @15
    @17
    cX
    c.an
    @14
    @2
    @8
    @15
    @17
    wceq
    @2
    @5
    @8
    @10
    simpl1
    @2
    @5
    @8
    @10
    simpl3
    cA
    cP
    @17
    cH
    c.or
    cK
    c.le
    cW
    lhpmcvr2.l
    lhpmcvr2.j
    @17
    eqid
    #
    lhpmcvr2.a
    lhpmcvr2.h
    lhpjat2
    syl2anc
    oveq2d
    @14
    cK
    col
    wcel
    #
    @3
    @18
    cX
    wceq
    @14
    @0
    @24
    @20
    cK
    hlol
    syl
    @21
    cB
    @17
    cK
    c.an
    cX
    lhpmcvr2.b
    lhpmcvr2.m
    @23
    olm11
    syl2anc
    3eqtrd
    @9
    @13
    wa
    #
    cP
    @12
    cX
    c.le
    @25
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    cP
    @12
    c.le
    wbr
    @25
    @0
    @26
    @0
    @1
    @5
    @8
    @13
    simpl1l
    cK
    hllat
    syl
    #
    @25
    @6
    @27
    @6
    @7
    @2
    @5
    @13
    simpl3l
    cA
    cB
    cP
    cK
    lhpmcvr2.b
    lhpmcvr2.a
    atbase
    syl
    @25
    @26
    @3
    @19
    @28
    @29
    @3
    @4
    @2
    @8
    @13
    simpl2l
    @25
    @1
    @19
    @0
    @1
    @5
    @8
    @13
    simpl1r
    @22
    syl
    cB
    cK
    c.an
    cX
    cW
    lhpmcvr2.b
    lhpmcvr2.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    c.le
    cP
    @11
    lhpmcvr2.b
    lhpmcvr2.l
    lhpmcvr2.j
    latlej1
    syl3anc
    @9
    @13
    simpr
    breqtrd
    impbida
end
