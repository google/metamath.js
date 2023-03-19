include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
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
include "lsmub2.mm"
include "simp3.mm"
include "sstrd.mm"

theorem dihord2b
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( X e. B /\ Y e. B ) /\ ( ( J ` Q ) .(+) ( I ` ( X ./\ W ) ) ) C_ ( ( J ` R ) .(+) ( I ` ( Y ./\ W ) ) ) ) -> ( I ` ( X ./\ W ) ) C_ ( ( J ` R ) .(+) ( I ` ( Y ./\ W ) ) ) )

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
    cJ
    cfv
    #
    cX
    cW
    c.an
    co
    #
    cI
    cfv
    #
    c.po
    co
    #
    cR
    cJ
    cfv
    cY
    cW
    c.an
    co
    cI
    cfv
    c.po
    co
    #
    wss
    #
    w3a
    #
    @11
    @12
    @13
    @15
    @9
    cU
    csubg
    cfv
    #
    wcel
    @11
    @16
    wcel
    @11
    @12
    wss
    @15
    cU
    clss
    cfv
    #
    @16
    @9
    @15
    cU
    clmod
    wcel
    @17
    @16
    wss
    @15
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
    @14
    simp11
    #
    dvhlmod
    @17
    cU
    @17
    eqid
    #
    lsssssubg
    syl
    #
    @15
    @2
    @3
    @9
    @17
    wcel
    @18
    @2
    @3
    @4
    @8
    @14
    simp12
    cA
    cQ
    @17
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
    @19
    diclss
    syl2anc
    sseldd
    @15
    @17
    @16
    @11
    @20
    @15
    @2
    @10
    cB
    wcel
    #
    @10
    cW
    c.le
    wbr
    #
    @11
    @17
    wcel
    @18
    @15
    cK
    clat
    wcel
    #
    @6
    cW
    cB
    wcel
    #
    @21
    @15
    @0
    @23
    @0
    @1
    @3
    @4
    @8
    @14
    simp11l
    cK
    hllat
    syl
    #
    @5
    @6
    @7
    @14
    simp2l
    #
    @15
    @1
    @24
    @0
    @1
    @3
    @4
    @8
    @14
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
    @15
    @23
    @6
    @24
    @22
    @25
    @26
    @27
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
    @17
    cU
    cH
    cI
    cK
    c.le
    cW
    @10
    dihjust.b
    dihjust.l
    dihjust.h
    dihjust.u
    dihjust.i
    @19
    diblss
    syl12anc
    sseldd
    c.po
    @9
    @11
    cU
    dihjust.s
    lsmub2
    syl2anc
    @5
    @8
    @14
    simp3
    sstrd
end
