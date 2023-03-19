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
include "csubg.mm"
include "clss.mm"
include "clmod.mm"
include "simp11.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lsssssubg.mm"
include "syl.mm"
include "simp12.mm"
include "diclss.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "simp2l.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latmle2.mm"
include "diblss.mm"
include "syl12anc.mm"
include "lsmub1.mm"
include "simp33.mm"
include "sstrd.mm"
include "wb.mm"
include "simp13.mm"
include "simp2r.mm"
include "jca.mm"
include "cdlemn.mm"
include "syl13anc.mm"
include "mpbird.mm"

theorem dihord2a
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
  let cY: class Y
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( X e. B /\ Y e. B ) /\ ( ( Q .\/ ( X ./\ W ) ) = X /\ ( R .\/ ( Y ./\ W ) ) = Y /\ ( ( J ` Q ) .(+) ( I ` ( X ./\ W ) ) ) C_ ( ( J ` R ) .(+) ( I ` ( Y ./\ W ) ) ) ) ) -> Q .<_ ( R .\/ ( Y ./\ W ) ) )

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
    cQ
    cW
    c.le
    wbr
    wn
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
    w3a
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cQ
    cX
    cW
    c.an
    co
    #
    c.or
    co
    cX
    wceq
    #
    cR
    cY
    cW
    c.an
    co
    #
    c.or
    co
    #
    cY
    wceq
    #
    cQ
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
    cR
    cJ
    cfv
    @11
    cI
    cfv
    c.po
    co
    #
    wss
    #
    w3a
    #
    w3a
    #
    cQ
    @12
    c.le
    wbr
    #
    @14
    @17
    wss
    #
    @20
    @14
    @16
    @17
    @20
    @14
    cU
    csubg
    cfv
    #
    wcel
    @15
    @23
    wcel
    @14
    @16
    wss
    @20
    cU
    clss
    cfv
    #
    @23
    @14
    @20
    cU
    clmod
    wcel
    @24
    @23
    wss
    @20
    cU
    cH
    cK
    cW
    dihjust.h
    dihjust.u
    @2
    @3
    @4
    @8
    @19
    simp11
    #
    dvhlmod
    @24
    cU
    @24
    eqid
    #
    lsssssubg
    syl
    #
    @20
    @2
    @3
    @14
    @24
    wcel
    @25
    @2
    @3
    @4
    @8
    @19
    simp12
    #
    cA
    cQ
    @24
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
    @26
    diclss
    syl2anc
    sseldd
    @20
    @24
    @23
    @15
    @27
    @20
    @2
    @9
    cB
    wcel
    #
    @9
    cW
    c.le
    wbr
    #
    @15
    @24
    wcel
    @25
    @20
    cK
    clat
    wcel
    #
    @6
    cW
    cB
    wcel
    #
    @29
    @20
    @0
    @31
    @0
    @1
    @3
    @4
    @8
    @19
    simp11l
    cK
    hllat
    syl
    #
    @5
    @6
    @7
    @19
    simp2l
    #
    @20
    @1
    @32
    @0
    @1
    @3
    @4
    @8
    @19
    simp11r
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
    @20
    @31
    @6
    @32
    @30
    @33
    @34
    @35
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
    cB
    @24
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
    @26
    diblss
    syl12anc
    sseldd
    c.po
    @14
    @15
    cU
    dihjust.s
    lsmub1
    syl2anc
    @5
    @8
    @10
    @13
    @18
    simp33
    sstrd
    @20
    @2
    @4
    @3
    @11
    cB
    wcel
    #
    @11
    cW
    c.le
    wbr
    #
    wa
    @21
    @22
    wb
    @25
    @2
    @3
    @4
    @8
    @19
    simp13
    @28
    @20
    @36
    @37
    @20
    @31
    @7
    @32
    @36
    @33
    @5
    @6
    @7
    @19
    simp2r
    #
    @35
    cB
    cK
    c.an
    cY
    cW
    dihjust.b
    dihjust.m
    latmcl
    syl3anc
    @20
    @31
    @7
    @32
    @37
    @33
    @38
    @35
    cB
    cK
    c.le
    c.an
    cY
    cW
    dihjust.b
    dihjust.l
    dihjust.m
    latmle2
    syl3anc
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
    @11
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
    mpbird
end
