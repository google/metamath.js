include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "cdic.mm"
include "co.mm"
include "cdib.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3l.mm"
include "simp3r.mm"
include "wb.mm"
include "lhpmcvr3.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "eqid.mm"
include "dihvalcq.mm"
include "syl112anc.mm"
include "dihvalcqat.mm"
include "syl2anc.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latmle2.mm"
include "dihvalb.mm"
include "syl12anc.mm"
include "oveq12d.mm"
include "eqtr4d.mm"

theorem dihvalcq2
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  assume dihvalcq2.b: |- B = ( Base ` K )
  assume dihvalcq2.l: |- .<_ = ( le ` K )
  assume dihvalcq2.j: |- .\/ = ( join ` K )
  assume dihvalcq2.m: |- ./\ = ( meet ` K )
  assume dihvalcq2.a: |- A = ( Atoms ` K )
  assume dihvalcq2.h: |- H = ( LHyp ` K )
  assume dihvalcq2.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihvalcq2.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihvalcq2.p: |- .(+) = ( LSSum ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ Q .<_ X ) ) -> ( I ` X ) = ( ( I ` Q ) .(+) ( I ` ( X ./\ W ) ) ) )

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
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    cQ
    cX
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cX
    cI
    cfv
    #
    cQ
    cW
    cK
    cdic
    cfv
    cfv
    #
    cfv
    #
    cX
    cW
    c.an
    co
    #
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    #
    c.po
    co
    #
    cQ
    cI
    cfv
    #
    @13
    cI
    cfv
    #
    c.po
    co
    @9
    @2
    @5
    @6
    cQ
    @13
    c.or
    co
    cX
    wceq
    #
    @10
    @16
    wceq
    @2
    @5
    @8
    simp1
    #
    @2
    @5
    @8
    simp2
    #
    @2
    @5
    @6
    @7
    simp3l
    #
    @9
    @7
    @19
    @2
    @5
    @6
    @7
    simp3r
    @9
    @2
    @5
    @6
    @7
    @19
    wb
    @20
    @21
    @22
    cA
    cB
    cQ
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    dihvalcq2.b
    dihvalcq2.l
    dihvalcq2.j
    dihvalcq2.m
    dihvalcq2.a
    dihvalcq2.h
    lhpmcvr3
    syl3anc
    mpbid
    cA
    cB
    @11
    @14
    c.po
    cQ
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cX
    dihvalcq2.b
    dihvalcq2.l
    dihvalcq2.j
    dihvalcq2.m
    dihvalcq2.a
    dihvalcq2.h
    dihvalcq2.i
    @14
    eqid
    #
    @11
    eqid
    #
    dihvalcq2.u
    dihvalcq2.p
    dihvalcq
    syl112anc
    @9
    @17
    @12
    @18
    @15
    c.po
    @9
    @2
    @6
    @17
    @12
    wceq
    @20
    @22
    cA
    cQ
    cH
    cI
    @11
    cK
    c.le
    cW
    dihvalcq2.l
    dihvalcq2.a
    dihvalcq2.h
    @24
    dihvalcq2.i
    dihvalcqat
    syl2anc
    @9
    @2
    @13
    cB
    wcel
    #
    @13
    cW
    c.le
    wbr
    #
    @18
    @15
    wceq
    @20
    @9
    cK
    clat
    wcel
    #
    @3
    cW
    cB
    wcel
    #
    @25
    @9
    @0
    @27
    @0
    @1
    @5
    @8
    simp1l
    cK
    hllat
    syl
    #
    @2
    @3
    @4
    @8
    simp2l
    #
    @9
    @1
    @28
    @0
    @1
    @5
    @8
    simp1r
    cB
    cH
    cK
    cW
    dihvalcq2.b
    dihvalcq2.h
    lhpbase
    syl
    #
    cB
    cK
    c.an
    cX
    cW
    dihvalcq2.b
    dihvalcq2.m
    latmcl
    syl3anc
    @9
    @27
    @3
    @28
    @26
    @29
    @30
    @31
    cB
    cK
    c.le
    c.an
    cX
    cW
    dihvalcq2.b
    dihvalcq2.l
    dihvalcq2.m
    latmle2
    syl3anc
    cB
    @14
    cH
    cI
    cK
    c.le
    chlt
    cW
    @13
    dihvalcq2.b
    dihvalcq2.l
    dihvalcq2.h
    dihvalcq2.i
    @23
    dihvalb
    syl12anc
    oveq12d
    eqtr4d
end
