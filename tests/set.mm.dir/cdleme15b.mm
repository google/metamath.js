include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cp0.mm"
include "cfv.mm"
include "oveq2i.mm"
include "cbs.mm"
include "wceq.mm"
include "simp11l.mm"
include "simp12l.mm"
include "simp21l.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "syl.mm"
include "hlatlej1.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "col.mm"
include "hlol.mm"
include "clat.mm"
include "hllat.mm"
include "atbase.mm"
include "latjcl.mm"
include "simp13l.mm"
include "latmrot.mm"
include "syl13anc.mm"
include "simp31.mm"
include "wi.mm"
include "simp23l.mm"
include "necomd.mm"
include "hlatexch1.mm"
include "mtod.mm"
include "cal.mm"
include "wb.mm"
include "hlatl.mm"
include "atnle.mm"
include "mpbid.mm"
include "olm02.mm"
include "syl2anc.mm"
include "3eqtrrd.mm"
include "eqtr4d.mm"
include "cdleme9b.mm"
include "latlej2.mm"
include "atmod2i2.mm"
include "olj02.mm"
include "3eqtr3d.mm"

theorem cdleme15b
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
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
  let cW: class W
  let cX: class X
  assume cdleme12.l: |- .<_ = ( le ` K )
  assume cdleme12.j: |- .\/ = ( join ` K )
  assume cdleme12.m: |- ./\ = ( meet ` K )
  assume cdleme12.a: |- A = ( Atoms ` K )
  assume cdleme12.h: |- H = ( LHyp ` K )
  assume cdleme12.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme12.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme12.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme15.c: |- C = ( ( P .\/ S ) ./\ W )
  assume cdleme15.x: |- X = ( ( P .\/ T ) ./\ W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ S =/= T ) ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ -. U .<_ ( S .\/ T ) ) ) -> ( ( P .\/ C ) ./\ ( Q .\/ C ) ) = C )

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
    cT
    cW
    c.le
    wbr
    wn
    wa
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
    w3a
    #
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    cT
    @18
    c.le
    wbr
    wn
    #
    cU
    cS
    cT
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    cP
    cC
    c.or
    co
    #
    cQ
    c.an
    co
    #
    cC
    c.or
    co
    #
    cK
    cp0
    cfv
    #
    cC
    c.or
    co
    #
    @25
    cQ
    cC
    c.or
    co
    c.an
    co
    #
    cC
    @24
    @26
    @28
    cC
    c.or
    @24
    @26
    cP
    cS
    c.or
    co
    #
    cP
    cW
    c.or
    co
    #
    c.an
    co
    #
    cQ
    c.an
    co
    #
    @28
    @24
    @25
    @33
    cQ
    c.an
    @24
    @25
    cP
    @31
    cW
    c.an
    co
    #
    c.or
    co
    #
    @33
    cC
    @35
    cP
    c.or
    cdleme15.c
    oveq2i
    @24
    @0
    @3
    @31
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @37
    wcel
    #
    cP
    @31
    c.le
    wbr
    #
    @36
    @33
    wceq
    @0
    @1
    @5
    @8
    @17
    @23
    simp11l
    #
    @3
    @4
    @2
    @8
    @17
    @23
    simp12l
    #
    @24
    @0
    @3
    @10
    @38
    @41
    @42
    @10
    @11
    @13
    @16
    @9
    @23
    simp21l
    #
    cA
    @37
    c.or
    cK
    cP
    cS
    @37
    eqid
    #
    cdleme12.j
    cdleme12.a
    hlatjcl
    syl3anc
    #
    @24
    @1
    @39
    @0
    @1
    @5
    @8
    @17
    @23
    simp11r
    #
    @37
    cH
    cK
    cW
    @44
    cdleme12.h
    lhpbase
    syl
    #
    @24
    @0
    @3
    @10
    @40
    @41
    @42
    @43
    cA
    cP
    cS
    c.or
    cK
    c.le
    cdleme12.l
    cdleme12.j
    cdleme12.a
    hlatlej1
    syl3anc
    cA
    @37
    cP
    c.or
    cK
    c.le
    c.an
    @31
    cW
    @44
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    atmod3i1
    syl131anc
    syl5eq
    oveq1d
    @24
    @34
    cQ
    @31
    c.an
    co
    #
    @32
    c.an
    co
    #
    @28
    @32
    c.an
    co
    #
    @28
    @24
    cK
    col
    wcel
    #
    @38
    @32
    @37
    wcel
    #
    cQ
    @37
    wcel
    #
    @34
    @49
    wceq
    @24
    @0
    @51
    @41
    cK
    hlol
    syl
    #
    @45
    @24
    cK
    clat
    wcel
    #
    cP
    @37
    wcel
    #
    @39
    @52
    @24
    @0
    @55
    @41
    cK
    hllat
    syl
    #
    @24
    @3
    @56
    @42
    cA
    @37
    cP
    cK
    @44
    cdleme12.a
    atbase
    syl
    #
    @47
    @37
    c.or
    cK
    cP
    cW
    @44
    cdleme12.j
    latjcl
    syl3anc
    #
    @24
    @6
    @53
    @6
    @7
    @2
    @5
    @17
    @23
    simp13l
    #
    cA
    @37
    cQ
    cK
    @44
    cdleme12.a
    atbase
    syl
    @37
    cK
    c.an
    @31
    @32
    cQ
    @44
    cdleme12.m
    latmrot
    syl13anc
    @24
    @48
    @28
    @32
    c.an
    @24
    cQ
    @31
    c.le
    wbr
    #
    wn
    #
    @48
    @28
    wceq
    #
    @24
    @61
    @19
    @9
    @17
    @20
    @21
    @22
    simp31
    @24
    @0
    @6
    @10
    @3
    cQ
    cP
    wne
    @61
    @19
    wi
    @41
    @60
    @43
    @42
    @24
    cP
    cQ
    @14
    @15
    @12
    @13
    @9
    @23
    simp23l
    necomd
    cA
    cQ
    cS
    cP
    c.or
    cK
    c.le
    cdleme12.l
    cdleme12.j
    cdleme12.a
    hlatexch1
    syl131anc
    mtod
    @24
    cK
    cal
    wcel
    #
    @6
    @38
    @62
    @63
    wb
    @24
    @0
    @64
    @41
    cK
    hlatl
    syl
    @60
    @45
    cA
    @37
    cQ
    cK
    c.le
    c.an
    @31
    @28
    @44
    cdleme12.l
    cdleme12.m
    @28
    eqid
    #
    cdleme12.a
    atnle
    syl3anc
    mpbid
    oveq1d
    @24
    @51
    @52
    @50
    @28
    wceq
    @54
    @59
    @37
    cK
    c.an
    @32
    @28
    @44
    cdleme12.m
    @65
    olm02
    syl2anc
    3eqtrrd
    eqtr4d
    oveq1d
    @24
    @0
    @6
    @25
    @37
    wcel
    #
    cC
    @37
    wcel
    #
    cC
    @25
    c.le
    wbr
    #
    @27
    @30
    wceq
    @41
    @60
    @24
    @55
    @56
    @67
    @66
    @57
    @58
    @24
    @0
    @3
    @10
    @1
    @67
    @41
    @42
    @43
    @46
    cA
    @37
    cC
    cP
    cS
    cH
    c.or
    cK
    c.an
    cW
    @44
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme15.c
    cdleme9b
    syl13anc
    #
    @37
    c.or
    cK
    cP
    cC
    @44
    cdleme12.j
    latjcl
    syl3anc
    @69
    @24
    @55
    @56
    @67
    @68
    @57
    @58
    @69
    @37
    c.or
    cK
    c.le
    cP
    cC
    @44
    cdleme12.l
    cdleme12.j
    latlej2
    syl3anc
    cA
    @37
    cQ
    c.or
    cK
    c.le
    c.an
    @25
    cC
    @44
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    atmod2i2
    syl131anc
    @24
    @51
    @67
    @29
    cC
    wceq
    @54
    @69
    @37
    c.or
    cK
    cC
    @28
    @44
    cdleme12.j
    @65
    olj02
    syl2anc
    3eqtr3d
end
