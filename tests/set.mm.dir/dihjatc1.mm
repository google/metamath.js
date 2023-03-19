include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "simp11.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp12.mm"
include "simp13.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "simp2l.mm"
include "atbase.mm"
include "latjcl.mm"
include "simp2.mm"
include "simp3l.mm"
include "dihmeetlem6.mm"
include "syl32anc.mm"
include "dihmeetlem5.mm"
include "breq1d.mm"
include "mtbid.mm"
include "latlej2.mm"
include "dihvalcq2.mm"
include "syl122anc.mm"
include "cp0.mm"
include "eqid.mm"
include "lhpmat.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "simp3r.mm"
include "atmod1i2.mm"
include "syl131anc.mm"
include "col.mm"
include "hlol.mm"
include "olj01.mm"
include "3eqtr3d.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem dihjatc1
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
  let cY: class Y
  assume dihjatc1.b: |- B = ( Base ` K )
  assume dihjatc1.l: |- .<_ = ( le ` K )
  assume dihjatc1.h: |- H = ( LHyp ` K )
  assume dihjatc1.j: |- .\/ = ( join ` K )
  assume dihjatc1.m: |- ./\ = ( meet ` K )
  assume dihjatc1.a: |- A = ( Atoms ` K )
  assume dihjatc1.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjatc1.s: |- .(+) = ( LSSum ` U )
  assume dihjatc1.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ X e. B /\ Y e. B ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( Q .<_ X /\ ( X ./\ Y ) .<_ W ) ) -> ( I ` ( ( X ./\ Y ) .\/ Q ) ) = ( ( I ` Q ) .(+) ( I ` ( X ./\ Y ) ) ) )

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
    cY
    cB
    wcel
    #
    w3a
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
    cQ
    cX
    c.le
    wbr
    #
    cX
    cY
    c.an
    co
    #
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    @10
    cQ
    c.or
    co
    #
    cI
    cfv
    #
    cQ
    cI
    cfv
    #
    @14
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
    @16
    @10
    cI
    cfv
    #
    c.po
    co
    @13
    @2
    @14
    cB
    wcel
    #
    @14
    cW
    c.le
    wbr
    #
    wn
    @8
    cQ
    @14
    c.le
    wbr
    #
    @15
    @19
    wceq
    @2
    @3
    @4
    @8
    @12
    simp11
    #
    @13
    cK
    clat
    wcel
    #
    @10
    cB
    wcel
    #
    cQ
    cB
    wcel
    #
    @21
    @13
    @0
    @25
    @0
    @1
    @3
    @4
    @8
    @12
    simp11l
    #
    cK
    hllat
    syl
    #
    @13
    @25
    @3
    @4
    @26
    @29
    @2
    @3
    @4
    @8
    @12
    simp12
    #
    @2
    @3
    @4
    @8
    @12
    simp13
    #
    cB
    cK
    c.an
    cX
    cY
    dihjatc1.b
    dihjatc1.m
    latmcl
    syl3anc
    #
    @13
    @6
    @27
    @5
    @6
    @7
    @12
    simp2l
    #
    cA
    cB
    cQ
    cK
    dihjatc1.b
    dihjatc1.a
    atbase
    syl
    #
    cB
    c.or
    cK
    @10
    cQ
    dihjatc1.b
    dihjatc1.j
    latjcl
    syl3anc
    @13
    cX
    cY
    cQ
    c.or
    co
    c.an
    co
    #
    cW
    c.le
    wbr
    #
    @22
    @13
    @2
    @3
    @4
    @8
    @9
    @36
    wn
    @24
    @30
    @31
    @5
    @8
    @12
    simp2
    #
    @5
    @8
    @9
    @11
    simp3l
    #
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
    cY
    dihjatc1.b
    dihjatc1.l
    dihjatc1.h
    dihjatc1.j
    dihjatc1.m
    dihjatc1.a
    dihmeetlem6
    syl32anc
    @13
    @35
    @14
    cW
    c.le
    @13
    @0
    @3
    @4
    @6
    @9
    @35
    @14
    wceq
    @28
    @30
    @31
    @33
    @38
    cA
    cB
    cQ
    c.or
    cK
    c.le
    c.an
    cX
    cY
    dihjatc1.b
    dihjatc1.l
    dihjatc1.j
    dihjatc1.m
    dihjatc1.a
    dihmeetlem5
    syl32anc
    breq1d
    mtbid
    @37
    @13
    @25
    @26
    @27
    @23
    @29
    @32
    @34
    cB
    c.or
    cK
    c.le
    @10
    cQ
    dihjatc1.b
    dihjatc1.l
    dihjatc1.j
    latlej2
    syl3anc
    cA
    cB
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
    @14
    dihjatc1.b
    dihjatc1.l
    dihjatc1.j
    dihjatc1.m
    dihjatc1.a
    dihjatc1.h
    dihjatc1.i
    dihjatc1.u
    dihjatc1.s
    dihvalcq2
    syl122anc
    @13
    @18
    @20
    @16
    c.po
    @13
    @17
    @10
    cI
    @13
    @10
    cQ
    cW
    c.an
    co
    #
    c.or
    co
    #
    @10
    cK
    cp0
    cfv
    #
    c.or
    co
    #
    @17
    @10
    @13
    @39
    @41
    @10
    c.or
    @13
    @2
    @8
    @39
    @41
    wceq
    @24
    @37
    cA
    cQ
    cH
    cK
    c.le
    c.an
    cW
    @41
    dihjatc1.l
    dihjatc1.m
    @41
    eqid
    #
    dihjatc1.a
    dihjatc1.h
    lhpmat
    syl2anc
    oveq2d
    @13
    @0
    @6
    @26
    cW
    cB
    wcel
    #
    @11
    @40
    @17
    wceq
    @28
    @33
    @32
    @13
    @1
    @44
    @0
    @1
    @3
    @4
    @8
    @12
    simp11r
    cB
    cH
    cK
    cW
    dihjatc1.b
    dihjatc1.h
    lhpbase
    syl
    @5
    @8
    @9
    @11
    simp3r
    cA
    cB
    cQ
    c.or
    cK
    c.le
    c.an
    @10
    cW
    dihjatc1.b
    dihjatc1.l
    dihjatc1.j
    dihjatc1.m
    dihjatc1.a
    atmod1i2
    syl131anc
    @13
    cK
    col
    wcel
    #
    @26
    @42
    @10
    wceq
    @13
    @0
    @45
    @28
    cK
    hlol
    syl
    @32
    cB
    c.or
    cK
    @10
    @41
    dihjatc1.b
    dihjatc1.j
    @43
    olj01
    syl2anc
    3eqtr3d
    fveq2d
    oveq2d
    eqtrd
end
