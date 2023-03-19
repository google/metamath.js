include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "col.mm"
include "wceq.mm"
include "simp11l.mm"
include "hlol.mm"
include "syl.mm"
include "clat.mm"
include "hllat.mm"
include "simp2ll.mm"
include "atbase.mm"
include "simp11r.mm"
include "jca.mm"
include "simp13.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp2rl.mm"
include "simp12.mm"
include "ltrncnv.mm"
include "ltrnco.mm"
include "lhpbase.mm"
include "latmassOLD.mm"
include "syl13anc.mm"
include "simp2r.mm"
include "lhpmat.mm"
include "oveq1d.mm"
include "trlle.mm"
include "atmod4i2.mm"
include "syl131anc.mm"
include "olj02.mm"
include "3eqtr3rd.mm"
include "oveq2d.mm"
include "simp2l.mm"
include "simp33.mm"
include "necomd.mm"
include "trlcnv.mm"
include "neeqtrrd.mm"
include "simp31.mm"
include "ltrncnvnid.mm"
include "trlcone.mm"
include "syl112anc.mm"
include "simp32.mm"
include "trlnidat.mm"
include "trlcoat.mm"
include "lhp2at0.mm"
include "syl322anc.mm"
include "3eqtr2rd.mm"
include "oveq1i.mm"
include "syl6reqr.mm"

theorem cdlemh2
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let c.0: class .0.
  assume cdlemh.b: |- B = ( Base ` K )
  assume cdlemh.l: |- .<_ = ( le ` K )
  assume cdlemh.j: |- .\/ = ( join ` K )
  assume cdlemh.m: |- ./\ = ( meet ` K )
  assume cdlemh.a: |- A = ( Atoms ` K )
  assume cdlemh.h: |- H = ( LHyp ` K )
  assume cdlemh.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemh.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemh.s: |- S = ( ( P .\/ ( R ` G ) ) ./\ ( Q .\/ ( R ` ( G o. `' F ) ) ) )
  assume cdlemh.z: |- .0. = ( 0. ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) /\ ( R ` F ) =/= ( R ` G ) ) ) -> ( S ./\ W ) = .0. )

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
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    w3a
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
    wa
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    cG
    @13
    wne
    #
    cF
    cR
    cfv
    #
    cG
    cR
    cfv
    #
    wne
    #
    w3a
    #
    w3a
    #
    c.0
    cP
    @17
    c.or
    co
    #
    cQ
    cG
    cF
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    cW
    c.an
    co
    #
    cS
    cW
    c.an
    co
    @20
    @27
    @21
    @25
    cW
    c.an
    co
    #
    c.an
    co
    #
    @21
    @24
    c.an
    co
    #
    c.0
    @20
    cK
    col
    wcel
    #
    @21
    cB
    wcel
    #
    @25
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @27
    @29
    wceq
    @20
    @0
    @31
    @0
    @1
    @3
    @4
    @12
    @19
    simp11l
    #
    cK
    hlol
    syl
    #
    @20
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    @17
    cB
    wcel
    #
    @32
    @20
    @0
    @37
    @35
    cK
    hllat
    syl
    #
    @20
    @6
    @38
    @6
    @7
    @11
    @5
    @19
    simp2ll
    cA
    cB
    cP
    cK
    cdlemh.b
    cdlemh.a
    atbase
    syl
    @20
    @2
    @4
    @39
    @20
    @0
    @1
    @35
    @0
    @1
    @3
    @4
    @12
    @19
    simp11r
    #
    jca
    #
    @2
    @3
    @4
    @12
    @19
    simp13
    #
    cB
    cR
    cT
    cG
    cH
    cK
    cW
    cdlemh.b
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlcl
    syl2anc
    cB
    c.or
    cK
    cP
    @17
    cdlemh.b
    cdlemh.j
    latjcl
    syl3anc
    @20
    @37
    cQ
    cB
    wcel
    #
    @24
    cB
    wcel
    #
    @33
    @40
    @20
    @9
    @44
    @9
    @10
    @8
    @5
    @19
    simp2rl
    #
    cA
    cB
    cQ
    cK
    cdlemh.b
    cdlemh.a
    atbase
    syl
    @20
    @2
    @23
    cT
    wcel
    #
    @45
    @42
    @20
    @2
    @4
    @22
    cT
    wcel
    #
    @47
    @42
    @43
    @20
    @2
    @3
    @48
    @42
    @2
    @3
    @4
    @12
    @19
    simp12
    #
    cT
    cF
    cH
    cK
    cW
    cdlemh.h
    cdlemh.t
    ltrncnv
    syl2anc
    #
    cT
    cG
    @22
    cH
    cK
    cW
    cdlemh.h
    cdlemh.t
    ltrnco
    syl3anc
    #
    cB
    cR
    cT
    @23
    cH
    cK
    cW
    cdlemh.b
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlcl
    syl2anc
    #
    cB
    c.or
    cK
    cQ
    @24
    cdlemh.b
    cdlemh.j
    latjcl
    syl3anc
    @20
    @1
    @34
    @41
    cB
    cH
    cK
    cW
    cdlemh.b
    cdlemh.h
    lhpbase
    syl
    #
    cB
    cK
    c.an
    @21
    @25
    cW
    cdlemh.b
    cdlemh.m
    latmassOLD
    syl13anc
    @20
    @24
    @28
    @21
    c.an
    @20
    cQ
    cW
    c.an
    co
    #
    @24
    c.or
    co
    #
    c.0
    @24
    c.or
    co
    #
    @28
    @24
    @20
    @54
    c.0
    @24
    c.or
    @20
    @2
    @11
    @54
    c.0
    wceq
    @42
    @5
    @8
    @11
    @19
    simp2r
    cA
    cQ
    cH
    cK
    c.le
    c.an
    cW
    c.0
    cdlemh.l
    cdlemh.m
    cdlemh.z
    cdlemh.a
    cdlemh.h
    lhpmat
    syl2anc
    oveq1d
    @20
    @0
    @9
    @45
    @34
    @24
    cW
    c.le
    wbr
    #
    @55
    @28
    wceq
    @35
    @46
    @52
    @53
    @20
    @2
    @47
    @57
    @42
    @51
    cR
    cT
    @23
    cH
    cK
    c.le
    cW
    cdlemh.l
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlle
    syl2anc
    #
    cA
    cB
    cQ
    c.or
    cK
    c.le
    c.an
    @24
    cW
    cdlemh.b
    cdlemh.l
    cdlemh.j
    cdlemh.m
    cdlemh.a
    atmod4i2
    syl131anc
    @20
    @31
    @45
    @56
    @24
    wceq
    @36
    @52
    cB
    c.or
    cK
    @24
    c.0
    cdlemh.b
    cdlemh.j
    cdlemh.z
    olj02
    syl2anc
    3eqtr3rd
    oveq2d
    @20
    @2
    @8
    @17
    @24
    wne
    #
    @17
    cA
    wcel
    #
    @17
    cW
    c.le
    wbr
    #
    @24
    cA
    wcel
    #
    @57
    @30
    c.0
    wceq
    @42
    @5
    @8
    @11
    @19
    simp2l
    @20
    @2
    @4
    @48
    wa
    #
    @17
    @22
    cR
    cfv
    #
    wne
    #
    @22
    @13
    wne
    #
    @59
    @42
    @20
    @4
    @48
    @43
    @50
    jca
    #
    @20
    @17
    @16
    @64
    @20
    @16
    @17
    @5
    @12
    @14
    @15
    @18
    simp33
    necomd
    @20
    @2
    @3
    @64
    @16
    wceq
    @42
    @49
    cR
    cT
    cF
    cH
    cK
    cW
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlcnv
    syl2anc
    neeqtrrd
    #
    @20
    @2
    @3
    @14
    @66
    @42
    @49
    @5
    @12
    @14
    @15
    @18
    simp31
    cB
    cT
    cF
    cH
    cK
    cW
    cdlemh.b
    cdlemh.h
    cdlemh.t
    ltrncnvnid
    syl3anc
    cB
    cR
    cT
    cG
    @22
    cH
    cK
    cW
    cdlemh.b
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlcone
    syl112anc
    @20
    @2
    @4
    @15
    @60
    @42
    @43
    @5
    @12
    @14
    @15
    @18
    simp32
    cA
    cB
    cR
    cT
    cG
    cH
    cK
    cW
    cdlemh.b
    cdlemh.a
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlnidat
    syl3anc
    @20
    @2
    @4
    @61
    @42
    @43
    cR
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemh.l
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlle
    syl2anc
    @20
    @2
    @63
    @65
    @62
    @42
    @67
    @68
    cA
    cR
    cT
    cG
    @22
    cH
    cK
    cW
    cdlemh.a
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlcoat
    syl3anc
    @58
    cA
    cP
    @17
    cH
    c.or
    cK
    c.le
    c.an
    @24
    cW
    c.0
    cdlemh.l
    cdlemh.j
    cdlemh.m
    cdlemh.z
    cdlemh.a
    cdlemh.h
    lhp2at0
    syl322anc
    3eqtr2rd
    cS
    @26
    cW
    c.an
    cdlemh.s
    oveq1i
    syl6reqr
end
