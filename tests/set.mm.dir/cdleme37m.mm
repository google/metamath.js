include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "simp1.mm"
include "simp23.mm"
include "simp32l.mm"
include "simp33l.mm"
include "simp21.mm"
include "simp32r.mm"
include "simp33r.mm"
include "simp31r.mm"
include "3jca.mm"
include "eqid.mm"
include "cdleme21k.mm"
include "syl132anc.mm"
include "simp11.mm"
include "simp12l.mm"
include "simp13l.mm"
include "cdleme4.mm"
include "syl131anc.mm"
include "cdleme2.mm"
include "syl13anc.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "simp11l.mm"
include "simp23l.mm"
include "simpld.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "syl6reqr.mm"
include "3eqtr4d.mm"

theorem cdleme37m
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  let cX: class X
  assume cdleme37.l: |- .<_ = ( le ` K )
  assume cdleme37.j: |- .\/ = ( join ` K )
  assume cdleme37.m: |- ./\ = ( meet ` K )
  assume cdleme37.a: |- A = ( Atoms ` K )
  assume cdleme37.h: |- H = ( LHyp ` K )
  assume cdleme37.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme37.e: |- E = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme37.d: |- D = ( ( u .\/ U ) ./\ ( Q .\/ ( ( P .\/ u ) ./\ W ) ) )
  assume cdleme37.v: |- V = ( ( t .\/ E ) ./\ W )
  assume cdleme37.x: |- X = ( ( u .\/ D ) ./\ W )
  assume cdleme37.c: |- C = ( ( S .\/ V ) ./\ ( E .\/ ( ( t .\/ S ) ./\ W ) ) )
  assume cdleme37.g: |- G = ( ( S .\/ X ) ./\ ( D .\/ ( ( u .\/ S ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( ( R .<_ ( P .\/ Q ) /\ S .<_ ( P .\/ Q ) ) /\ ( ( t e. A /\ -. t .<_ W ) /\ -. t .<_ ( P .\/ Q ) ) /\ ( ( u e. A /\ -. u .<_ W ) /\ -. u .<_ ( P .\/ Q ) ) ) ) -> C = G )

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
    cP
    cQ
    wne
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
    w3a
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cS
    @16
    c.le
    wbr
    #
    wa
    #
    vt
    cv
    #
    cA
    wcel
    #
    @20
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @20
    @16
    c.le
    wbr
    wn
    #
    wa
    #
    vu
    cv
    #
    cA
    wcel
    #
    @26
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @26
    @16
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    w3a
    #
    @16
    cE
    cS
    @20
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    @16
    cD
    cS
    @26
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    cC
    cG
    @33
    @9
    @14
    @23
    @29
    @10
    @24
    @30
    @18
    w3a
    @37
    @41
    wceq
    @9
    @15
    @32
    simp1
    @9
    @10
    @11
    @14
    @32
    simp23
    #
    @23
    @24
    @19
    @31
    @9
    @15
    simp32l
    #
    @29
    @30
    @19
    @25
    @9
    @15
    simp33l
    #
    @9
    @10
    @11
    @14
    @32
    simp21
    @33
    @24
    @30
    @18
    @23
    @24
    @19
    @31
    @9
    @15
    simp32r
    @29
    @30
    @19
    @25
    @9
    @15
    simp33r
    @17
    @18
    @25
    @31
    @9
    @15
    simp31r
    #
    3jca
    cA
    @35
    cP
    cQ
    cS
    @20
    @26
    cU
    cE
    cD
    cH
    c.or
    cK
    c.le
    c.an
    @37
    @41
    cW
    @39
    cdleme37.l
    cdleme37.j
    cdleme37.m
    cdleme37.a
    cdleme37.h
    cdleme37.u
    cdleme37.e
    cdleme37.d
    @35
    eqid
    @39
    eqid
    @37
    eqid
    @41
    eqid
    cdleme21k
    syl132anc
    @33
    @37
    cS
    cV
    c.or
    co
    #
    cE
    @20
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    cC
    @33
    @16
    @46
    @36
    @49
    c.an
    @33
    @16
    cS
    cU
    c.or
    co
    #
    @46
    @33
    @2
    @3
    @6
    @14
    @18
    @16
    @50
    wceq
    @2
    @5
    @8
    @15
    @32
    simp11
    #
    @3
    @4
    @2
    @8
    @15
    @32
    simp12l
    #
    @6
    @7
    @2
    @5
    @15
    @32
    simp13l
    #
    @42
    @45
    cA
    cP
    cQ
    cS
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme37.l
    cdleme37.j
    cdleme37.m
    cdleme37.a
    cdleme37.h
    cdleme37.u
    cdleme4
    syl131anc
    #
    @33
    cV
    cU
    cS
    c.or
    @33
    cV
    @20
    cE
    c.or
    co
    cW
    c.an
    co
    #
    cU
    cdleme37.v
    @33
    @2
    @3
    @6
    @23
    @55
    cU
    wceq
    @51
    @52
    @53
    @43
    cA
    cP
    cQ
    @20
    cU
    cE
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme37.l
    cdleme37.j
    cdleme37.m
    cdleme37.a
    cdleme37.h
    cdleme37.u
    cdleme37.e
    cdleme2
    syl13anc
    syl5eq
    oveq2d
    eqtr4d
    @33
    @35
    @48
    cE
    c.or
    @33
    @34
    @47
    cW
    c.an
    @33
    @0
    @12
    @21
    @34
    @47
    wceq
    @0
    @1
    @5
    @8
    @15
    @32
    simp11l
    #
    @12
    @13
    @10
    @11
    @9
    @32
    simp23l
    #
    @33
    @21
    @22
    @43
    simpld
    cA
    c.or
    cK
    cS
    @20
    cdleme37.j
    cdleme37.a
    hlatjcom
    syl3anc
    oveq1d
    oveq2d
    oveq12d
    cdleme37.c
    syl6reqr
    @33
    @41
    cS
    cX
    c.or
    co
    #
    cD
    @26
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    cG
    @33
    @16
    @58
    @40
    @61
    c.an
    @33
    @16
    @50
    @58
    @54
    @33
    cX
    cU
    cS
    c.or
    @33
    cX
    @26
    cD
    c.or
    co
    cW
    c.an
    co
    #
    cU
    cdleme37.x
    @33
    @2
    @3
    @6
    @29
    @62
    cU
    wceq
    @51
    @52
    @53
    @44
    cA
    cP
    cQ
    @26
    cU
    cD
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme37.l
    cdleme37.j
    cdleme37.m
    cdleme37.a
    cdleme37.h
    cdleme37.u
    cdleme37.d
    cdleme2
    syl13anc
    syl5eq
    oveq2d
    eqtr4d
    @33
    @39
    @60
    cD
    c.or
    @33
    @38
    @59
    cW
    c.an
    @33
    @0
    @12
    @27
    @38
    @59
    wceq
    @56
    @57
    @33
    @27
    @28
    @44
    simpld
    cA
    c.or
    cK
    cS
    @26
    cdleme37.j
    cdleme37.a
    hlatjcom
    syl3anc
    oveq1d
    oveq2d
    oveq12d
    cdleme37.g
    syl6reqr
    3eqtr4d
end
