include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp11r.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simp22l.mm"
include "eqid.mm"
include "cdleme1b.mm"
include "syl23anc.mm"
include "simp21l.mm"
include "cdlemedb.mm"
include "syl22anc.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp23l.mm"
include "latmcom.mm"
include "cdleme20l.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "simp23.mm"
include "simp22.mm"
include "simp31l.mm"
include "simp31r.mm"
include "necomd.mm"
include "jca.mm"
include "simp322.mm"
include "simp321.mm"
include "simp323.mm"
include "3jca.mm"
include "simp33l.mm"
include "hlatjcom.mm"
include "breq2d.mm"
include "mtbid.mm"
include "simp33r.mm"
include "syl333anc.mm"
include "3eqtr3d.mm"
include "3eqtr4g.mm"

theorem cdleme20m
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
  let cN: class N
  let cO: class O
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
  assume cdleme20.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ D ) )
  assume cdleme20.o: |- O = ( ( P .\/ Q ) ./\ ( G .\/ Y ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) ) /\ ( ( P =/= Q /\ S =/= T ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ R .<_ ( P .\/ Q ) ) /\ ( -. R .<_ ( S .\/ T ) /\ -. U .<_ ( S .\/ T ) ) ) ) -> N = O )

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
    #
    wn
    #
    cU
    @28
    c.le
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    w3a
    #
    @23
    cF
    cD
    c.or
    co
    #
    c.an
    co
    #
    @23
    cG
    cY
    c.or
    co
    #
    c.an
    co
    #
    cN
    cO
    @35
    @36
    @38
    c.an
    co
    #
    @38
    @36
    c.an
    co
    #
    @37
    @39
    @35
    cK
    clat
    wcel
    #
    @36
    cK
    cbs
    cfv
    #
    wcel
    #
    @38
    @43
    wcel
    #
    @40
    @41
    wceq
    @35
    @0
    @42
    @0
    @1
    @5
    @8
    @19
    @34
    simp11l
    #
    cK
    hllat
    syl
    #
    @35
    @42
    cF
    @43
    wcel
    #
    cD
    @43
    wcel
    #
    @44
    @47
    @35
    @0
    @1
    @3
    @6
    @13
    @48
    @46
    @0
    @1
    @5
    @8
    @19
    @34
    simp11r
    #
    @3
    @4
    @2
    @8
    @19
    @34
    simp12l
    #
    @6
    @7
    @2
    @5
    @19
    @34
    simp13l
    #
    @13
    @14
    @12
    @18
    @9
    @34
    simp22l
    #
    cA
    @43
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
    @43
    eqid
    #
    cdleme1b
    syl23anc
    @35
    @0
    @1
    @10
    @13
    @49
    @46
    @50
    @10
    @11
    @15
    @18
    @9
    @34
    simp21l
    #
    @53
    cA
    @43
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
    @54
    cdlemedb
    syl22anc
    @43
    c.or
    cK
    cF
    cD
    @54
    cdleme19.j
    latjcl
    syl3anc
    @35
    @42
    cG
    @43
    wcel
    #
    cY
    @43
    wcel
    #
    @45
    @47
    @35
    @0
    @1
    @3
    @6
    @16
    @56
    @46
    @50
    @51
    @52
    @16
    @17
    @12
    @15
    @9
    @34
    simp23l
    #
    cA
    @43
    cP
    cQ
    cT
    cU
    cG
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
    cdleme19.g
    @54
    cdleme1b
    syl23anc
    @35
    @0
    @1
    @10
    @16
    @57
    @46
    @50
    @55
    @58
    cA
    @43
    cY
    cR
    cT
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
    cdleme19.y
    @54
    cdlemedb
    syl22anc
    @43
    c.or
    cK
    cG
    cY
    @54
    cdleme19.j
    latjcl
    syl3anc
    @43
    cK
    c.an
    @36
    @38
    @54
    cdleme19.m
    latmcom
    syl3anc
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
    cdleme20l
    @35
    @2
    @5
    @8
    @12
    @18
    @15
    @20
    cT
    cS
    wne
    #
    wa
    @25
    @24
    @26
    w3a
    cR
    cT
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    cU
    @60
    c.le
    wbr
    #
    wn
    #
    wa
    @41
    @39
    wceq
    @2
    @5
    @8
    @19
    @34
    simp11
    @2
    @5
    @8
    @19
    @34
    simp12
    @2
    @5
    @8
    @19
    @34
    simp13
    @9
    @12
    @15
    @18
    @34
    simp21
    @9
    @12
    @15
    @18
    @34
    simp23
    @9
    @12
    @15
    @18
    @34
    simp22
    @35
    @20
    @59
    @20
    @21
    @27
    @33
    @9
    @19
    simp31l
    @35
    cS
    cT
    @20
    @21
    @27
    @33
    @9
    @19
    simp31r
    necomd
    jca
    @35
    @25
    @24
    @26
    @24
    @25
    @26
    @22
    @33
    @9
    @19
    simp322
    @24
    @25
    @26
    @22
    @33
    @9
    @19
    simp321
    @24
    @25
    @26
    @22
    @33
    @9
    @19
    simp323
    3jca
    @35
    @62
    @64
    @35
    @29
    @61
    @30
    @32
    @22
    @27
    @9
    @19
    simp33l
    @35
    @28
    @60
    cR
    c.le
    @35
    @0
    @13
    @16
    @28
    @60
    wceq
    @46
    @53
    @58
    cA
    c.or
    cK
    cS
    cT
    cdleme19.j
    cdleme19.a
    hlatjcom
    syl3anc
    #
    breq2d
    mtbid
    @35
    @31
    @63
    @30
    @32
    @22
    @27
    @9
    @19
    simp33r
    @35
    @28
    @60
    cU
    c.le
    @65
    breq2d
    mtbid
    jca
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
    @60
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
    @66
    eqid
    cdleme20l
    syl333anc
    3eqtr3d
    cdleme20.n
    cdleme20.o
    3eqtr4g
end
