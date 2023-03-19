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
include "simp11r.mm"
include "jca.mm"
include "simp23.mm"
include "simp212.mm"
include "simp12.mm"
include "simp13.mm"
include "simp211.mm"
include "simp331.mm"
include "simp332.mm"
include "necomd.mm"
include "simp311.mm"
include "simp313.mm"
include "simp312.mm"
include "3jca.mm"
include "simp22.mm"
include "cdlemkuat.mm"
include "syl333anc.mm"
include "atbase.mm"
include "simp213.mm"
include "simp333.mm"
include "simp32.mm"
include "simp22l.mm"
include "cdlemkvcl.mm"
include "syl231anc.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "ltrnco.mm"
include "trlcl.mm"
include "cdlemk7u.mm"
include "cdlemk10.mm"
include "wi.mm"
include "latjlej2.mm"
include "syl13anc.mm"
include "mpd.mm"
include "lattrd.mm"

theorem cdlemk11u
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let ve: setvar e
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cV: class V
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
  assume cdlemk1.u: |- U = ( e e. T |-> ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` e ) ) ./\ ( ( O ` P ) .\/ ( R ` ( e o. `' D ) ) ) ) ) )
  assume cdlemk1.v: |- V = ( ( ( G ` P ) .\/ ( X ` P ) ) ./\ ( ( R ` ( G o. `' D ) ) .\/ ( R ` ( X o. `' D ) ) ) )

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
  disjoint ./\ e
  disjoint .\/ e
  disjoint D e
  disjoint e j
  disjoint G e
  disjoint G j
  disjoint O e
  disjoint P e
  disjoint R e
  disjoint T e
  disjoint W e
  disjoint ./\ j
  disjoint .<_ j
  disjoint .\/ j
  disjoint A j
  disjoint D j
  disjoint F j
  disjoint H j
  disjoint K j
  disjoint N j
  disjoint O j
  disjoint P j
  disjoint R j
  disjoint T j
  disjoint W j
  disjoint F e
  disjoint X e
  disjoint X j
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ D e. T ) /\ ( ( N e. T /\ G e. T /\ X e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) /\ G =/= ( _I |` B ) ) /\ X =/= ( _I |` B ) /\ ( ( R ` D ) =/= ( R ` F ) /\ ( R ` G ) =/= ( R ` D ) /\ ( R ` X ) =/= ( R ` D ) ) ) ) -> ( ( U ` G ) ` P ) .<_ ( ( ( U ` X ) ` P ) .\/ ( R ` ( X o. `' G ) ) ) )

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
    cX
    @16
    wne
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
    #
    @22
    wne
    #
    cX
    cR
    cfv
    #
    @22
    wne
    #
    w3a
    #
    w3a
    #
    w3a
    #
    cB
    cK
    c.le
    cP
    cG
    cU
    cfv
    cfv
    #
    cP
    cX
    cU
    cfv
    cfv
    #
    cV
    c.or
    co
    #
    @32
    cX
    cG
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
    cdlemk1.b
    cdlemk1.l
    @30
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
    @29
    simp11l
    #
    cK
    hllat
    syl
    #
    @30
    @31
    cA
    wcel
    #
    @31
    cB
    wcel
    @30
    @2
    @14
    @7
    @3
    @4
    @6
    @23
    @22
    @24
    wne
    #
    wa
    @17
    @19
    @18
    w3a
    @12
    @41
    @30
    @0
    @1
    @39
    @0
    @1
    @3
    @4
    @15
    @29
    simp11r
    #
    jca
    #
    @5
    @9
    @12
    @14
    @29
    simp23
    #
    @6
    @7
    @8
    @12
    @14
    @5
    @29
    simp212
    #
    @2
    @3
    @4
    @15
    @29
    simp12
    #
    @2
    @3
    @4
    @15
    @29
    simp13
    #
    @6
    @7
    @8
    @12
    @14
    @5
    @29
    simp211
    #
    @30
    @23
    @42
    @23
    @25
    @27
    @20
    @21
    @5
    @15
    simp331
    #
    @30
    @24
    @22
    @23
    @25
    @27
    @20
    @21
    @5
    @15
    simp332
    necomd
    jca
    @30
    @17
    @19
    @18
    @17
    @18
    @19
    @21
    @28
    @5
    @15
    simp311
    #
    @17
    @18
    @19
    @21
    @28
    @5
    @15
    simp313
    @17
    @18
    @19
    @21
    @28
    @5
    @15
    simp312
    #
    3jca
    @5
    @9
    @12
    @14
    @29
    simp22
    #
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    cU
    ve
    vf
    vi
    vj
    cF
    cG
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
    cdlemk1.u
    cdlemkuat
    syl333anc
    cA
    cB
    @31
    cK
    cdlemk1.b
    cdlemk1.a
    atbase
    syl
    @30
    @38
    @32
    cB
    wcel
    #
    cV
    cB
    wcel
    #
    @33
    cB
    wcel
    @40
    @30
    @32
    cA
    wcel
    #
    @54
    @30
    @2
    @14
    @8
    @3
    @4
    @6
    @23
    @22
    @26
    wne
    #
    wa
    @17
    @21
    @18
    w3a
    @12
    @56
    @44
    @45
    @6
    @7
    @8
    @12
    @14
    @5
    @29
    simp213
    #
    @47
    @48
    @49
    @30
    @23
    @57
    @50
    @30
    @26
    @22
    @23
    @25
    @27
    @20
    @21
    @5
    @15
    simp333
    necomd
    jca
    @30
    @17
    @21
    @18
    @51
    @5
    @15
    @20
    @21
    @28
    simp32
    @52
    3jca
    @53
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    cU
    ve
    vf
    vi
    vj
    cF
    cX
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
    cdlemk1.u
    cdlemkuat
    syl333anc
    cA
    cB
    @32
    cK
    cdlemk1.b
    cdlemk1.a
    atbase
    syl
    #
    @30
    @0
    @1
    @4
    @7
    @8
    @10
    @55
    @39
    @43
    @48
    @46
    @58
    @10
    @11
    @9
    @14
    @5
    @29
    simp22l
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
    cV
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
    cdlemk1.v
    cdlemkvcl
    syl231anc
    #
    cB
    c.or
    cK
    @32
    cV
    cdlemk1.b
    cdlemk1.j
    latjcl
    syl3anc
    @30
    @38
    @54
    @36
    cB
    wcel
    #
    @37
    cB
    wcel
    @40
    @59
    @30
    @2
    @35
    cT
    wcel
    #
    @61
    @44
    @30
    @2
    @8
    @34
    cT
    wcel
    #
    @62
    @44
    @58
    @30
    @2
    @7
    @63
    @44
    @46
    cT
    cG
    cH
    cK
    cW
    cdlemk1.h
    cdlemk1.t
    ltrncnv
    syl2anc
    cT
    cX
    @34
    cH
    cK
    cW
    cdlemk1.h
    cdlemk1.t
    ltrnco
    syl3anc
    cB
    cR
    cT
    @35
    cH
    cK
    cW
    cdlemk1.b
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlcl
    syl2anc
    #
    cB
    c.or
    cK
    @32
    @36
    cdlemk1.b
    cdlemk1.j
    latjcl
    syl3anc
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    cU
    ve
    vf
    vi
    vj
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cV
    cW
    cX
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
    cdlemk1.u
    cdlemk1.v
    cdlemk7u
    @30
    cV
    @36
    c.le
    wbr
    #
    @33
    @37
    c.le
    wbr
    #
    @30
    @0
    @1
    @4
    @7
    @8
    @12
    @65
    @39
    @43
    @48
    @46
    @58
    @53
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
    cV
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
    cdlemk1.v
    cdlemk10
    syl231anc
    @30
    @38
    @55
    @61
    @54
    @65
    @66
    wi
    @40
    @60
    @64
    @59
    cB
    c.or
    cK
    c.le
    cV
    @36
    @32
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    latjlej2
    syl13anc
    mpd
    lattrd
end
