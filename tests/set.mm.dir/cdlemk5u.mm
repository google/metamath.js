include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp22l.mm"
include "simp1.mm"
include "simp211.mm"
include "simp22.mm"
include "simp23.mm"
include "3jca.mm"
include "simp3l1.mm"
include "simp3l2.mm"
include "simp3r1.mm"
include "cdlemkoatnle.mm"
include "simpld.mm"
include "syl3anc.mm"
include "hlatjcl.mm"
include "simp11.mm"
include "simp212.mm"
include "ltrnat.mm"
include "simp13.mm"
include "simp3r2.mm"
include "trlcocnvat.mm"
include "syl121anc.mm"
include "latmcl.mm"
include "trlnidat.mm"
include "simp213.mm"
include "simp3r3.mm"
include "cdlemk1u.mm"
include "wi.mm"
include "latmlem1.mm"
include "syl13anc.mm"
include "mpd.mm"
include "simp11r.mm"
include "cdlemk2.mm"
include "syl221anc.mm"
include "oveq2d.mm"
include "breqtrd.mm"
include "simp3l3.mm"
include "jca.mm"
include "cdlemk5a.mm"
include "syl233anc.mm"
include "lattrd.mm"

theorem cdlemk5u
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  assume cdlemk1.b: |- B = ( Base ` K )
  assume cdlemk1.l: |- .<_ = ( le ` K )
  assume cdlemk1.j: |- .\/ = ( join ` K )
  assume cdlemk1.m: |- ./\ = ( meet ` K )
  assume cdlemk1.a: |- A = ( Atoms ` K )
  assume cdlemk1.h: |- H = ( LHyp ` K )
  assume cdlemk1.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk1.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk1.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk1.o: |- O = ( S ` D )

  disjoint f i
  disjoint ./\ f
  disjoint ./\ i
  disjoint .<_ i
  disjoint .\/ f
  disjoint .\/ i
  disjoint A i
  disjoint D f
  disjoint D i
  disjoint F f
  disjoint F i
  disjoint H i
  disjoint K i
  disjoint N f
  disjoint N i
  disjoint P f
  disjoint P i
  disjoint R f
  disjoint R i
  disjoint T f
  disjoint T i
  disjoint W f
  disjoint W i
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ D e. T ) /\ ( ( N e. T /\ G e. T /\ X e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) /\ G =/= ( _I |` B ) ) /\ ( ( R ` D ) =/= ( R ` F ) /\ ( R ` G ) =/= ( R ` D ) /\ ( R ` X ) =/= ( R ` D ) ) ) ) -> ( ( P .\/ ( O ` P ) ) ./\ ( ( G ` P ) .\/ ( R ` ( G o. `' D ) ) ) ) .<_ ( ( X ` P ) .\/ ( R ` ( X o. `' D ) ) ) )

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
    cD
    cT
    wcel
    #
    w3a
    #
    cN
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    cX
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
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    #
    w3a
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    cD
    @16
    wne
    #
    cG
    @16
    wne
    #
    w3a
    #
    cD
    cR
    cfv
    #
    @13
    wne
    #
    cG
    cR
    cfv
    @21
    wne
    #
    cX
    cR
    cfv
    @21
    wne
    #
    w3a
    #
    wa
    #
    w3a
    #
    cB
    cK
    c.le
    cP
    cP
    cO
    cfv
    #
    c.or
    co
    #
    cP
    cG
    cfv
    #
    cG
    cD
    ccnv
    #
    ccom
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    cP
    cD
    cfv
    #
    @21
    c.or
    co
    #
    @35
    @32
    c.or
    co
    #
    c.an
    co
    #
    cP
    cX
    cfv
    #
    cX
    @31
    ccom
    cR
    cfv
    #
    c.or
    co
    #
    cdlemk1.b
    cdlemk1.l
    @27
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @3
    @4
    @15
    @26
    simp11l
    #
    cK
    hllat
    syl
    #
    @27
    @42
    @29
    cB
    wcel
    #
    @33
    cB
    wcel
    #
    @34
    cB
    wcel
    @44
    @27
    @0
    @10
    @28
    cA
    wcel
    #
    @45
    @43
    @10
    @11
    @9
    @14
    @5
    @26
    simp22l
    #
    @27
    @5
    @6
    @12
    @14
    w3a
    #
    @17
    @18
    @22
    w3a
    #
    @47
    @5
    @15
    @26
    simp1
    #
    @27
    @6
    @12
    @14
    @6
    @7
    @8
    @12
    @14
    @5
    @26
    simp211
    @5
    @9
    @12
    @14
    @26
    simp22
    #
    @5
    @9
    @12
    @14
    @26
    simp23
    3jca
    #
    @27
    @17
    @18
    @22
    @17
    @18
    @19
    @25
    @5
    @15
    simp3l1
    @17
    @18
    @19
    @25
    @5
    @15
    simp3l2
    #
    @22
    @23
    @24
    @20
    @5
    @15
    simp3r1
    3jca
    #
    @5
    @49
    @50
    w3a
    @47
    @28
    cW
    c.le
    wbr
    wn
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.m
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk1.s
    cdlemk1.o
    cdlemkoatnle
    simpld
    syl3anc
    cA
    cB
    c.or
    cK
    cP
    @28
    cdlemk1.b
    cdlemk1.j
    cdlemk1.a
    hlatjcl
    syl3anc
    #
    @27
    @0
    @30
    cA
    wcel
    #
    @32
    cA
    wcel
    #
    @46
    @43
    @27
    @2
    @7
    @10
    @57
    @2
    @3
    @4
    @15
    @26
    simp11
    #
    @6
    @7
    @8
    @12
    @14
    @5
    @26
    simp212
    #
    @48
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    ltrnat
    syl3anc
    @27
    @2
    @7
    @4
    @23
    @58
    @59
    @60
    @2
    @3
    @4
    @15
    @26
    simp13
    #
    @22
    @23
    @24
    @20
    @5
    @15
    simp3r2
    #
    cA
    cR
    cT
    cG
    cD
    cH
    cK
    cW
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlcocnvat
    syl121anc
    #
    cA
    cB
    c.or
    cK
    @30
    @32
    cdlemk1.b
    cdlemk1.j
    cdlemk1.a
    hlatjcl
    syl3anc
    #
    cB
    cK
    c.an
    @29
    @33
    cdlemk1.b
    cdlemk1.m
    latmcl
    syl3anc
    @27
    @42
    @36
    cB
    wcel
    #
    @37
    cB
    wcel
    #
    @38
    cB
    wcel
    @44
    @27
    @0
    @35
    cA
    wcel
    #
    @21
    cA
    wcel
    #
    @65
    @43
    @27
    @2
    @4
    @10
    @67
    @59
    @61
    @48
    cA
    cP
    cT
    cD
    cH
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    ltrnat
    syl3anc
    #
    @27
    @2
    @4
    @18
    @68
    @59
    @61
    @54
    cA
    cB
    cR
    cT
    cD
    cH
    cK
    cW
    cdlemk1.b
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlnidat
    syl3anc
    cA
    cB
    c.or
    cK
    @35
    @21
    cdlemk1.b
    cdlemk1.j
    cdlemk1.a
    hlatjcl
    syl3anc
    #
    @27
    @0
    @67
    @58
    @66
    @43
    @69
    @63
    cA
    cB
    c.or
    cK
    @35
    @32
    cdlemk1.b
    cdlemk1.j
    cdlemk1.a
    hlatjcl
    syl3anc
    cB
    cK
    c.an
    @36
    @37
    cdlemk1.b
    cdlemk1.m
    latmcl
    syl3anc
    @27
    @0
    @39
    cA
    wcel
    #
    @40
    cA
    wcel
    #
    @41
    cB
    wcel
    @43
    @27
    @2
    @8
    @10
    @71
    @59
    @6
    @7
    @8
    @12
    @14
    @5
    @26
    simp213
    #
    @48
    cA
    cP
    cT
    cX
    cH
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    ltrnat
    syl3anc
    @27
    @2
    @8
    @4
    @24
    @72
    @59
    @73
    @61
    @22
    @23
    @24
    @20
    @5
    @15
    simp3r3
    cA
    cR
    cT
    cX
    cD
    cH
    cK
    cW
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlcocnvat
    syl121anc
    cA
    cB
    c.or
    cK
    @39
    @40
    cdlemk1.b
    cdlemk1.j
    cdlemk1.a
    hlatjcl
    syl3anc
    @27
    @34
    @36
    @33
    c.an
    co
    #
    @38
    c.le
    @27
    @29
    @36
    c.le
    wbr
    #
    @34
    @74
    c.le
    wbr
    #
    @27
    @5
    @49
    @50
    @75
    @51
    @53
    @55
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.m
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk1.s
    cdlemk1.o
    cdlemk1u
    syl3anc
    @27
    @42
    @45
    @65
    @46
    @75
    @76
    wi
    @44
    @56
    @70
    @64
    cB
    cK
    c.le
    c.an
    @29
    @36
    @33
    cdlemk1.b
    cdlemk1.l
    cdlemk1.m
    latmlem1
    syl13anc
    mpd
    @27
    @33
    @37
    @36
    c.an
    @27
    @0
    @1
    @4
    @7
    @12
    @33
    @37
    wceq
    @43
    @0
    @1
    @3
    @4
    @15
    @26
    simp11r
    #
    @61
    @60
    @52
    cA
    cB
    cP
    cR
    cT
    cD
    cG
    cH
    c.or
    cK
    c.le
    cW
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk2
    syl221anc
    oveq2d
    breqtrd
    @27
    @0
    @1
    @4
    @7
    @8
    @23
    @18
    @19
    wa
    @12
    @38
    @41
    c.le
    wbr
    @43
    @77
    @61
    @60
    @73
    @62
    @27
    @18
    @19
    @54
    @17
    @18
    @19
    @25
    @5
    @15
    simp3l3
    jca
    @52
    cA
    cB
    cP
    cR
    cT
    cD
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk1.m
    cdlemk5a
    syl233anc
    lattrd
end
