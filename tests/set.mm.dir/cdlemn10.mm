include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp22l.mm"
include "atbase.mm"
include "simp21l.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp23l.mm"
include "latjcl.mm"
include "hlatlej2.mm"
include "cmee.mm"
include "cp1.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "hlatlej1.mm"
include "eqid.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "simp1.mm"
include "simp21.mm"
include "lhpjat2.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "3eqtrrd.mm"
include "simp31.mm"
include "trlval2.mm"
include "simp32.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "simp33.mm"
include "eqbrtrrd.mm"
include "wi.mm"
include "latmcl.mm"
include "latjlej2.mm"
include "syl13anc.mm"
include "mpd.mm"
include "eqbrtrd.mm"
include "lattrd.mm"

theorem cdlemn10
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let vg: setvar g
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  assume cdlemn10.b: |- B = ( Base ` K )
  assume cdlemn10.l: |- .<_ = ( le ` K )
  assume cdlemn10.j: |- .\/ = ( join ` K )
  assume cdlemn10.a: |- A = ( Atoms ` K )
  assume cdlemn10.h: |- H = ( LHyp ` K )
  assume cdlemn10.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemn10.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( S e. A /\ -. S .<_ W ) /\ ( X e. B /\ X .<_ W ) ) /\ ( g e. T /\ ( g ` Q ) = S /\ ( R ` g ) .<_ X ) ) -> S .<_ ( Q .\/ X ) )

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
    cS
    cA
    wcel
    #
    cS
    cW
    c.le
    wbr
    wn
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
    #
    wa
    #
    w3a
    #
    vg
    cv
    #
    cT
    wcel
    #
    cQ
    @13
    cfv
    #
    cS
    wceq
    #
    @13
    cR
    cfv
    #
    cX
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cB
    cK
    c.le
    cS
    cQ
    cS
    c.or
    co
    #
    cQ
    cX
    c.or
    co
    #
    cdlemn10.b
    cdlemn10.l
    @20
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @12
    @19
    simp1l
    #
    cK
    hllat
    syl
    #
    @20
    @6
    cS
    cB
    wcel
    @6
    @7
    @5
    @11
    @2
    @19
    simp22l
    #
    cA
    cB
    cS
    cK
    cdlemn10.b
    cdlemn10.a
    atbase
    syl
    @20
    @0
    @3
    @6
    @21
    cB
    wcel
    #
    @24
    @3
    @4
    @8
    @11
    @2
    @19
    simp21l
    #
    @26
    cA
    cB
    c.or
    cK
    cQ
    cS
    cdlemn10.b
    cdlemn10.j
    cdlemn10.a
    hlatjcl
    syl3anc
    #
    @20
    @23
    cQ
    cB
    wcel
    #
    @9
    @22
    cB
    wcel
    @25
    @20
    @3
    @30
    @28
    cA
    cB
    cQ
    cK
    cdlemn10.b
    cdlemn10.a
    atbase
    syl
    #
    @9
    @10
    @5
    @8
    @2
    @19
    simp23l
    #
    cB
    c.or
    cK
    cQ
    cX
    cdlemn10.b
    cdlemn10.j
    latjcl
    syl3anc
    @20
    @0
    @3
    @6
    cS
    @21
    c.le
    wbr
    @24
    @28
    @26
    cA
    cQ
    cS
    c.or
    cK
    c.le
    cdlemn10.l
    cdlemn10.j
    cdlemn10.a
    hlatlej2
    syl3anc
    @20
    @21
    cQ
    @21
    cW
    cK
    cmee
    cfv
    #
    co
    #
    c.or
    co
    #
    @22
    c.le
    @20
    @35
    @21
    cQ
    cW
    c.or
    co
    #
    @33
    co
    #
    @21
    cK
    cp1
    cfv
    #
    @33
    co
    #
    @21
    @20
    @0
    @3
    @27
    cW
    cB
    wcel
    #
    cQ
    @21
    c.le
    wbr
    #
    @35
    @37
    wceq
    @24
    @28
    @29
    @20
    @1
    @40
    @0
    @1
    @12
    @19
    simp1r
    cB
    cH
    cK
    cW
    cdlemn10.b
    cdlemn10.h
    lhpbase
    syl
    #
    @20
    @0
    @3
    @6
    @41
    @24
    @28
    @26
    cA
    cQ
    cS
    c.or
    cK
    c.le
    cdlemn10.l
    cdlemn10.j
    cdlemn10.a
    hlatlej1
    syl3anc
    cA
    cB
    cQ
    c.or
    cK
    c.le
    @33
    @21
    cW
    cdlemn10.b
    cdlemn10.l
    cdlemn10.j
    @33
    eqid
    #
    cdlemn10.a
    atmod3i1
    syl131anc
    @20
    @36
    @38
    @21
    @33
    @20
    @2
    @5
    @36
    @38
    wceq
    @2
    @12
    @19
    simp1
    #
    @2
    @5
    @8
    @11
    @19
    simp21
    #
    cA
    cQ
    @38
    cH
    c.or
    cK
    c.le
    cW
    cdlemn10.l
    cdlemn10.j
    @38
    eqid
    #
    cdlemn10.a
    cdlemn10.h
    lhpjat2
    syl2anc
    oveq2d
    @20
    cK
    col
    wcel
    #
    @27
    @39
    @21
    wceq
    @20
    @0
    @47
    @24
    cK
    hlol
    syl
    @29
    cB
    @38
    cK
    @33
    @21
    cdlemn10.b
    @43
    @46
    olm11
    syl2anc
    3eqtrrd
    @20
    @34
    cX
    c.le
    wbr
    #
    @35
    @22
    c.le
    wbr
    #
    @20
    @17
    @34
    cX
    c.le
    @20
    @17
    cQ
    @15
    c.or
    co
    #
    cW
    @33
    co
    #
    @34
    @20
    @2
    @14
    @5
    @17
    @51
    wceq
    @44
    @2
    @12
    @14
    @16
    @18
    simp31
    @45
    cA
    cQ
    cR
    cT
    @13
    cH
    c.or
    cK
    c.le
    @33
    cW
    cdlemn10.l
    cdlemn10.j
    @43
    cdlemn10.a
    cdlemn10.h
    cdlemn10.t
    cdlemn10.r
    trlval2
    syl3anc
    @20
    @50
    @21
    cW
    @33
    @20
    @15
    cS
    cQ
    c.or
    @2
    @12
    @14
    @16
    @18
    simp32
    oveq2d
    oveq1d
    eqtrd
    @2
    @12
    @14
    @16
    @18
    simp33
    eqbrtrrd
    @20
    @23
    @34
    cB
    wcel
    #
    @9
    @30
    @48
    @49
    wi
    @25
    @20
    @23
    @27
    @40
    @52
    @25
    @29
    @42
    cB
    cK
    @33
    @21
    cW
    cdlemn10.b
    @43
    latmcl
    syl3anc
    @32
    @31
    cB
    c.or
    cK
    c.le
    @34
    cX
    cQ
    cdlemn10.b
    cdlemn10.l
    cdlemn10.j
    latjlej2
    syl13anc
    mpd
    eqbrtrd
    lattrd
end
