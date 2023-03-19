include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "cdleme20i.mm"
include "clln.mm"
include "cfv.mm"
include "wb.mm"
include "simp11l.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21l.mm"
include "simp22l.mm"
include "simp22r.mm"
include "simp31l.mm"
include "simp321.mm"
include "simp323.mm"
include "cdleme20l1.mm"
include "syl333anc.mm"
include "simp23l.mm"
include "simp23r.mm"
include "simp322.mm"
include "eqid.mm"
include "simp12l.mm"
include "simp13l.mm"
include "llni2.mm"
include "syl31anc.mm"
include "cdleme20l2.mm"
include "simp22.mm"
include "simp21.mm"
include "cdleme20k.mm"
include "syl322anc.mm"
include "llnexchb2.mm"
include "syl132anc.mm"
include "mpbid.mm"
include "clat.mm"
include "cbs.mm"
include "hllat.mm"
include "syl.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp11r.mm"
include "cdleme1b.mm"
include "syl23anc.mm"
include "cdlemedb.mm"
include "syl22anc.mm"
include "latjcl.mm"
include "latmcom.mm"
include "eqtr4d.mm"

theorem cdleme20l
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  let cY: class Y
  assume cdleme19.l: |- .<_ = ( le ` K )
  assume cdleme19.j: |- .\/ = ( join ` K )
  assume cdleme19.m: |- ./\ = ( meet ` K )
  assume cdleme19.a: |- A = ( Atoms ` K )
  assume cdleme19.h: |- H = ( LHyp ` K )
  assume cdleme19.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme19.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme19.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme19.d: |- D = ( ( R .\/ S ) ./\ W )
  assume cdleme19.y: |- Y = ( ( R .\/ T ) ./\ W )
  assume cdleme20.v: |- V = ( ( S .\/ T ) ./\ W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) ) /\ ( ( P =/= Q /\ S =/= T ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ R .<_ ( P .\/ Q ) ) /\ ( -. R .<_ ( S .\/ T ) /\ -. U .<_ ( S .\/ T ) ) ) ) -> ( ( F .\/ D ) ./\ ( G .\/ Y ) ) = ( ( P .\/ Q ) ./\ ( F .\/ D ) ) )

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
    w3a
    #
    cR
    cA
    wcel
    #
    cR
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
    cT
    cA
    wcel
    #
    cT
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
    cQ
    wne
    #
    cS
    cT
    wne
    #
    wa
    #
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cT
    @23
    c.le
    wbr
    wn
    #
    cR
    @23
    c.le
    wbr
    #
    w3a
    #
    cR
    cS
    cT
    c.or
    co
    #
    c.le
    wbr
    wn
    cU
    @28
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    w3a
    #
    cF
    cD
    c.or
    co
    #
    cG
    cY
    c.or
    co
    #
    c.an
    co
    #
    @32
    @23
    c.an
    co
    #
    @23
    @32
    c.an
    co
    #
    @31
    @34
    @23
    c.le
    wbr
    #
    @34
    @35
    wceq
    #
    cA
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cY
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.f
    cdleme19.g
    cdleme19.d
    cdleme19.y
    cdleme20.v
    cdleme20i
    @31
    @0
    @32
    cK
    clln
    cfv
    #
    wcel
    #
    @33
    @39
    wcel
    #
    @23
    @39
    wcel
    #
    @34
    cA
    wcel
    @32
    @23
    wne
    #
    @37
    @38
    wb
    @0
    @1
    @5
    @8
    @19
    @30
    simp11l
    #
    @31
    @2
    @5
    @8
    @10
    @13
    @14
    @20
    @24
    @26
    @40
    @2
    @5
    @8
    @19
    @30
    simp11
    #
    @2
    @5
    @8
    @19
    @30
    simp12
    #
    @2
    @5
    @8
    @19
    @30
    simp13
    #
    @10
    @11
    @15
    @18
    @9
    @30
    simp21l
    #
    @13
    @14
    @12
    @18
    @9
    @30
    simp22l
    #
    @13
    @14
    @12
    @18
    @9
    @30
    simp22r
    @20
    @21
    @27
    @29
    @9
    @19
    simp31l
    #
    @24
    @25
    @26
    @22
    @29
    @9
    @19
    simp321
    #
    @24
    @25
    @26
    @22
    @29
    @9
    @19
    simp323
    #
    cA
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cY
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.f
    cdleme19.g
    cdleme19.d
    cdleme19.y
    cdleme20.v
    cdleme20l1
    syl333anc
    @31
    @2
    @5
    @8
    @10
    @16
    @17
    @20
    @25
    @26
    @41
    @45
    @46
    @47
    @48
    @16
    @17
    @12
    @15
    @9
    @30
    simp23l
    @16
    @17
    @12
    @15
    @9
    @30
    simp23r
    @50
    @24
    @25
    @26
    @22
    @29
    @9
    @19
    simp322
    @52
    cA
    cY
    cP
    cQ
    cR
    cT
    cS
    cU
    cG
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cT
    cS
    c.or
    co
    cW
    c.an
    co
    #
    cW
    cD
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.g
    cdleme19.f
    cdleme19.y
    cdleme19.d
    @53
    eqid
    cdleme20l1
    syl333anc
    @31
    @0
    @3
    @6
    @20
    @42
    @44
    @3
    @4
    @2
    @8
    @19
    @30
    simp12l
    #
    @6
    @7
    @2
    @5
    @19
    @30
    simp13l
    #
    @50
    cA
    cP
    cQ
    c.or
    cK
    @39
    cdleme19.j
    cdleme19.a
    @39
    eqid
    #
    llni2
    syl31anc
    cA
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cY
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.f
    cdleme19.g
    cdleme19.d
    cdleme19.y
    cdleme20.v
    cdleme20l2
    @31
    @2
    @3
    @6
    @15
    @12
    @24
    @26
    @43
    @45
    @54
    @55
    @9
    @12
    @15
    @18
    @30
    simp22
    @9
    @12
    @15
    @18
    @30
    simp21
    @51
    @52
    cA
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cY
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.f
    cdleme19.g
    cdleme19.d
    cdleme19.y
    cdleme20.v
    cdleme20k
    syl322anc
    cA
    c.or
    cK
    c.le
    c.an
    @39
    @32
    @33
    @23
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    @56
    llnexchb2
    syl132anc
    mpbid
    @31
    cK
    clat
    wcel
    #
    @23
    cK
    cbs
    cfv
    #
    wcel
    #
    @32
    @58
    wcel
    #
    @36
    @35
    wceq
    @31
    @0
    @57
    @44
    cK
    hllat
    syl
    #
    @31
    @0
    @3
    @6
    @59
    @44
    @54
    @55
    cA
    @58
    c.or
    cK
    cP
    cQ
    @58
    eqid
    #
    cdleme19.j
    cdleme19.a
    hlatjcl
    syl3anc
    @31
    @57
    cF
    @58
    wcel
    #
    cD
    @58
    wcel
    #
    @60
    @61
    @31
    @0
    @1
    @3
    @6
    @13
    @63
    @44
    @0
    @1
    @5
    @8
    @19
    @30
    simp11r
    #
    @54
    @55
    @49
    cA
    @58
    cP
    cQ
    cS
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.f
    @62
    cdleme1b
    syl23anc
    @31
    @0
    @1
    @10
    @13
    @64
    @44
    @65
    @48
    @49
    cA
    @58
    cD
    cR
    cS
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.d
    @62
    cdlemedb
    syl22anc
    @58
    c.or
    cK
    cF
    cD
    @62
    cdleme19.j
    latjcl
    syl3anc
    @58
    cK
    c.an
    @23
    @32
    @62
    cdleme19.m
    latmcom
    syl3anc
    eqtr4d
end
