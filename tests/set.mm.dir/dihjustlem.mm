include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "wss.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp21l.mm"
include "atbase.mm"
include "simp23.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latlej1.mm"
include "simp3.mm"
include "breqtrd.mm"
include "wb.mm"
include "simp1.mm"
include "simp22.mm"
include "simp21.mm"
include "latmle2.mm"
include "jca.mm"
include "cdlemn.mm"
include "syl13anc.mm"
include "mpbid.mm"
include "csubg.mm"
include "clss.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lsssssubg.mm"
include "diclss.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "diblss.mm"
include "syl12anc.mm"
include "lsmub2.mm"
include "lsmcl.mm"
include "lsmlub.mm"
include "mpbi2and.mm"

theorem dihjustlem
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cH: class H
  let cI: class I
  let cJ: class J
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  assume dihjust.b: |- B = ( Base ` K )
  assume dihjust.l: |- .<_ = ( le ` K )
  assume dihjust.j: |- .\/ = ( join ` K )
  assume dihjust.m: |- ./\ = ( meet ` K )
  assume dihjust.a: |- A = ( Atoms ` K )
  assume dihjust.h: |- H = ( LHyp ` K )
  assume dihjust.i: |- I = ( ( DIsoB ` K ) ` W )
  assume dihjust.J: |- J = ( ( DIsoC ` K ) ` W )
  assume dihjust.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjust.s: |- .(+) = ( LSSum ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) /\ X e. B ) /\ ( Q .\/ ( X ./\ W ) ) = ( R .\/ ( X ./\ W ) ) ) -> ( ( J ` Q ) .(+) ( I ` ( X ./\ W ) ) ) C_ ( ( J ` R ) .(+) ( I ` ( X ./\ W ) ) ) )

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
    cR
    cW
    c.le
    wbr
    wn
    wa
    #
    cX
    cB
    wcel
    #
    w3a
    #
    cQ
    cX
    cW
    c.an
    co
    #
    c.or
    co
    #
    cR
    @9
    c.or
    co
    #
    wceq
    #
    w3a
    #
    cQ
    cJ
    cfv
    #
    cR
    cJ
    cfv
    #
    @9
    cI
    cfv
    #
    c.po
    co
    #
    wss
    #
    @16
    @17
    wss
    #
    @14
    @16
    c.po
    co
    @17
    wss
    #
    @13
    cQ
    @11
    c.le
    wbr
    #
    @18
    @13
    cQ
    @10
    @11
    c.le
    @13
    cK
    clat
    wcel
    #
    cQ
    cB
    wcel
    #
    @9
    cB
    wcel
    #
    cQ
    @10
    c.le
    wbr
    @13
    @0
    @22
    @0
    @1
    @8
    @12
    simp1l
    cK
    hllat
    syl
    #
    @13
    @3
    @23
    @3
    @4
    @6
    @7
    @2
    @12
    simp21l
    cA
    cB
    cQ
    cK
    dihjust.b
    dihjust.a
    atbase
    syl
    @13
    @22
    @7
    cW
    cB
    wcel
    #
    @24
    @25
    @2
    @5
    @6
    @7
    @12
    simp23
    #
    @13
    @1
    @26
    @0
    @1
    @8
    @12
    simp1r
    cB
    cH
    cK
    cW
    dihjust.b
    dihjust.h
    lhpbase
    syl
    #
    cB
    cK
    c.an
    cX
    cW
    dihjust.b
    dihjust.m
    latmcl
    syl3anc
    #
    cB
    c.or
    cK
    c.le
    cQ
    @9
    dihjust.b
    dihjust.l
    dihjust.j
    latlej1
    syl3anc
    @2
    @8
    @12
    simp3
    breqtrd
    @13
    @2
    @6
    @5
    @24
    @9
    cW
    c.le
    wbr
    #
    wa
    @21
    @18
    wb
    @2
    @8
    @12
    simp1
    #
    @2
    @5
    @6
    @7
    @12
    simp22
    #
    @2
    @5
    @6
    @7
    @12
    simp21
    #
    @13
    @24
    @30
    @29
    @13
    @22
    @7
    @26
    @30
    @25
    @27
    @28
    cB
    cK
    c.le
    c.an
    cX
    cW
    dihjust.b
    dihjust.l
    dihjust.m
    latmle2
    syl3anc
    #
    jca
    cA
    cB
    c.po
    cR
    cQ
    cU
    cH
    cI
    cJ
    c.or
    cK
    c.le
    cW
    @9
    dihjust.b
    dihjust.l
    dihjust.j
    dihjust.a
    dihjust.h
    dihjust.i
    dihjust.J
    dihjust.u
    dihjust.s
    cdlemn
    syl13anc
    mpbid
    @13
    @15
    cU
    csubg
    cfv
    #
    wcel
    @16
    @35
    wcel
    #
    @19
    @13
    cU
    clss
    cfv
    #
    @35
    @15
    @13
    cU
    clmod
    wcel
    #
    @37
    @35
    wss
    @13
    cU
    cH
    cK
    cW
    dihjust.h
    dihjust.u
    @31
    dvhlmod
    #
    @37
    cU
    @37
    eqid
    #
    lsssssubg
    syl
    #
    @13
    @2
    @6
    @15
    @37
    wcel
    #
    @31
    @32
    cA
    cR
    @37
    cU
    cH
    cJ
    cK
    c.le
    cW
    dihjust.l
    dihjust.a
    dihjust.h
    dihjust.u
    dihjust.J
    @40
    diclss
    syl2anc
    #
    sseldd
    @13
    @37
    @35
    @16
    @41
    @13
    @2
    @24
    @30
    @16
    @37
    wcel
    #
    @31
    @29
    @34
    cB
    @37
    cU
    cH
    cI
    cK
    c.le
    cW
    @9
    dihjust.b
    dihjust.l
    dihjust.h
    dihjust.u
    dihjust.i
    @40
    diblss
    syl12anc
    #
    sseldd
    #
    c.po
    @15
    @16
    cU
    dihjust.s
    lsmub2
    syl2anc
    @13
    @14
    @35
    wcel
    @36
    @17
    @35
    wcel
    @18
    @19
    wa
    @20
    wb
    @13
    @37
    @35
    @14
    @41
    @13
    @2
    @5
    @14
    @37
    wcel
    @31
    @33
    cA
    cQ
    @37
    cU
    cH
    cJ
    cK
    c.le
    cW
    dihjust.l
    dihjust.a
    dihjust.h
    dihjust.u
    dihjust.J
    @40
    diclss
    syl2anc
    sseldd
    @46
    @13
    @37
    @35
    @17
    @41
    @13
    @38
    @42
    @44
    @17
    @37
    wcel
    @39
    @43
    @45
    c.po
    @37
    @15
    @16
    cU
    @40
    dihjust.s
    lsmcl
    syl3anc
    sseldd
    c.po
    @14
    @16
    @17
    cU
    dihjust.s
    lsmlub
    syl3anc
    mpbi2and
end
