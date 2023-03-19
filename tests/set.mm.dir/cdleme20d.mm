include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "col.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simp11l.mm"
include "hlol.mm"
include "syl.mm"
include "clat.mm"
include "hllat.mm"
include "simp11r.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simp21l.mm"
include "eqid.mm"
include "cdleme1b.mm"
include "syl23anc.mm"
include "simp22l.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "lhpbase.mm"
include "simp23l.mm"
include "hlatjcl.mm"
include "atbase.mm"
include "latmassOLD.mm"
include "syl13anc.mm"
include "hlatlej2.mm"
include "wi.mm"
include "latjlej1.mm"
include "mpd.mm"
include "wb.mm"
include "latleeqm1.mm"
include "mpbid.mm"
include "oveq1d.mm"
include "syl6reqr.mm"
include "latm32.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp31.mm"
include "simp32l.mm"
include "simp32r.mm"
include "cdleme16.mm"
include "syl132anc.mm"
include "eqtrd.mm"
include "simp23.mm"
include "simp33.mm"
include "cdleme20c.mm"
include "syl232anc.mm"
include "latmcom.mm"
include "oveq2d.mm"
include "3eqtr4rd.mm"

theorem cdleme20d
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( ( P =/= Q /\ S =/= T ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) ) /\ R .<_ ( P .\/ Q ) ) ) -> ( ( F .\/ G ) ./\ ( D .\/ Y ) ) = V )

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
    #
    cT
    cW
    c.le
    wbr
    wn
    #
    wa
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
    w3a
    #
    cP
    cQ
    wne
    cS
    cT
    wne
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
    @21
    c.le
    wbr
    wn
    #
    wa
    #
    cR
    @21
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cF
    cG
    c.or
    co
    #
    cW
    c.an
    co
    #
    cR
    cS
    c.or
    co
    #
    cT
    c.or
    co
    #
    c.an
    co
    #
    @28
    cW
    @31
    c.an
    co
    #
    c.an
    co
    #
    cV
    @28
    cD
    cY
    c.or
    co
    #
    c.an
    co
    @27
    cK
    col
    wcel
    #
    @28
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
    @31
    @37
    wcel
    #
    @32
    @34
    wceq
    @27
    @0
    @36
    @0
    @1
    @5
    @8
    @19
    @26
    simp11l
    #
    cK
    hlol
    syl
    #
    @27
    cK
    clat
    wcel
    #
    cF
    @37
    wcel
    #
    cG
    @37
    wcel
    #
    @38
    @27
    @0
    @43
    @41
    cK
    hllat
    syl
    #
    @27
    @0
    @1
    @3
    @6
    @10
    @44
    @41
    @0
    @1
    @5
    @8
    @19
    @26
    simp11r
    #
    @3
    @4
    @2
    @8
    @19
    @26
    simp12l
    #
    @6
    @7
    @2
    @5
    @19
    @26
    simp13l
    #
    @10
    @11
    @15
    @18
    @9
    @26
    simp21l
    #
    cA
    @37
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
    @37
    eqid
    #
    cdleme1b
    syl23anc
    @27
    @0
    @1
    @3
    @6
    @13
    @45
    @41
    @47
    @48
    @49
    @13
    @14
    @12
    @18
    @9
    @26
    simp22l
    #
    cA
    @37
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
    @51
    cdleme1b
    syl23anc
    @37
    c.or
    cK
    cF
    cG
    @51
    cdleme19.j
    latjcl
    syl3anc
    @27
    @1
    @39
    @47
    @37
    cH
    cK
    cW
    @51
    cdleme19.h
    lhpbase
    syl
    #
    @27
    @43
    @30
    @37
    wcel
    #
    cT
    @37
    wcel
    #
    @40
    @46
    @27
    @0
    @16
    @10
    @54
    @41
    @16
    @17
    @12
    @15
    @9
    @26
    simp23l
    #
    @50
    cA
    @37
    c.or
    cK
    cR
    cS
    @51
    cdleme19.j
    cdleme19.a
    hlatjcl
    syl3anc
    #
    @27
    @13
    @55
    @52
    cA
    @37
    cT
    cK
    @51
    cdleme19.a
    atbase
    syl
    #
    @37
    c.or
    cK
    @30
    cT
    @51
    cdleme19.j
    latjcl
    syl3anc
    #
    @37
    cK
    c.an
    @28
    cW
    @31
    @51
    cdleme19.m
    latmassOLD
    syl13anc
    @27
    cV
    cS
    cT
    c.or
    co
    #
    @31
    c.an
    co
    #
    cW
    c.an
    co
    #
    @32
    @27
    @62
    @60
    cW
    c.an
    co
    #
    cV
    @27
    @61
    @60
    cW
    c.an
    @27
    @60
    @31
    c.le
    wbr
    #
    @61
    @60
    wceq
    #
    @27
    cS
    @30
    c.le
    wbr
    #
    @64
    @27
    @0
    @16
    @10
    @66
    @41
    @56
    @50
    cA
    cR
    cS
    c.or
    cK
    c.le
    cdleme19.l
    cdleme19.j
    cdleme19.a
    hlatlej2
    syl3anc
    @27
    @43
    cS
    @37
    wcel
    #
    @54
    @55
    @66
    @64
    wi
    @46
    @27
    @10
    @67
    @50
    cA
    @37
    cS
    cK
    @51
    cdleme19.a
    atbase
    syl
    @57
    @58
    @37
    c.or
    cK
    c.le
    cS
    @30
    cT
    @51
    cdleme19.l
    cdleme19.j
    latjlej1
    syl13anc
    mpd
    @27
    @43
    @60
    @37
    wcel
    #
    @40
    @64
    @65
    wb
    @46
    @27
    @0
    @10
    @13
    @68
    @41
    @50
    @52
    cA
    @37
    c.or
    cK
    cS
    cT
    @51
    cdleme19.j
    cdleme19.a
    hlatjcl
    syl3anc
    #
    @59
    @37
    cK
    c.le
    c.an
    @60
    @31
    @51
    cdleme19.l
    cdleme19.m
    latleeqm1
    syl3anc
    mpbid
    oveq1d
    cdleme20.v
    syl6reqr
    @27
    @62
    @63
    @31
    c.an
    co
    #
    @32
    @27
    @36
    @68
    @40
    @39
    @62
    @70
    wceq
    @42
    @69
    @59
    @53
    @37
    cK
    c.an
    @60
    @31
    cW
    @51
    cdleme19.m
    latm32
    syl13anc
    @27
    @63
    @29
    @31
    c.an
    @27
    @9
    @12
    @15
    @20
    @22
    @23
    @63
    @29
    wceq
    @9
    @19
    @26
    simp1
    @9
    @12
    @15
    @18
    @26
    simp21
    #
    @9
    @12
    @15
    @18
    @26
    simp22
    @9
    @19
    @20
    @24
    @25
    simp31
    @22
    @23
    @20
    @25
    @9
    @19
    simp32l
    #
    @22
    @23
    @20
    @25
    @9
    @19
    simp32r
    cA
    cP
    cQ
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
    cW
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.f
    cdleme19.g
    cdleme16
    syl132anc
    oveq1d
    eqtrd
    eqtrd
    @27
    @35
    @33
    @28
    c.an
    @27
    @35
    @31
    cW
    c.an
    co
    #
    @33
    @27
    @0
    @1
    @18
    @12
    @13
    @22
    @25
    @35
    @73
    wceq
    @41
    @47
    @9
    @12
    @15
    @18
    @26
    simp23
    @71
    @52
    @72
    @9
    @19
    @20
    @24
    @25
    simp33
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
    cdleme20c
    syl232anc
    @27
    @43
    @40
    @39
    @73
    @33
    wceq
    @46
    @59
    @53
    @37
    cK
    c.an
    @31
    cW
    @51
    cdleme19.m
    latmcom
    syl3anc
    eqtrd
    oveq2d
    3eqtr4rd
end
