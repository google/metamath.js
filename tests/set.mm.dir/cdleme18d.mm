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
include "wrex.mm"
include "eleq1.mm"
include "breq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "3anbi1d.mm"
include "3anbi2d.mm"
include "simp11.mm"
include "simp21.mm"
include "simp13l.mm"
include "simp22.mm"
include "simp322.mm"
include "eqid.mm"
include "cdleme17d1.mm"
include "syl131anc.mm"
include "simp23.mm"
include "simp323.mm"
include "eqtr4d.mm"
include "syl6bi.mm"
include "eqeq12i.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "syl5bb.mm"
include "sylibrd.mm"
include "com12.mm"
include "3anbi23d.mm"
include "simp11l.mm"
include "simp11r.mm"
include "simp12.mm"
include "simp31.mm"
include "simp33.mm"
include "cdleme18c.mm"
include "syl233anc.mm"
include "wo.mm"
include "simp321.mm"
include "simp12l.mm"
include "simp21l.mm"
include "simp21r.mm"
include "cdleme0nex.mm"
include "syl332anc.mm"
include "mpjaod.mm"

theorem cdleme18d
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vr: setvar r
  assume cdleme18d.l: |- .<_ = ( le ` K )
  assume cdleme18d.j: |- .\/ = ( join ` K )
  assume cdleme18d.m: |- ./\ = ( meet ` K )
  assume cdleme18d.a: |- A = ( Atoms ` K )
  assume cdleme18d.h: |- H = ( LHyp ` K )
  assume cdleme18d.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme18d.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme18d.g: |- G = ( ( P .\/ Q ) ./\ ( F .\/ ( ( R .\/ S ) ./\ W ) ) )
  assume cdleme18d.d: |- D = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme18d.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( R .\/ T ) ./\ W ) ) )

  disjoint A r
  disjoint D r
  disjoint F r
  disjoint .\/ r
  disjoint .<_ r
  disjoint ./\ r
  disjoint P r
  disjoint Q r
  disjoint R r
  disjoint S r
  disjoint T r
  disjoint W r
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) ) /\ ( P =/= Q /\ ( R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> G = E )

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
    #
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
    #
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
    #
    wn
    #
    wa
    #
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
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
    w3a
    #
    cP
    cQ
    wne
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
    @20
    c.le
    wbr
    wn
    #
    cT
    @20
    c.le
    wbr
    wn
    #
    w3a
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @25
    c.or
    co
    cQ
    @25
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    wn
    #
    w3a
    #
    w3a
    #
    cR
    cP
    wceq
    #
    cG
    cE
    wceq
    #
    cR
    cQ
    wceq
    #
    @29
    @28
    @30
    @29
    @28
    @20
    cF
    cP
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
    #
    @20
    cD
    cP
    cT
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
    wceq
    #
    @30
    @29
    @28
    @11
    @6
    @16
    @17
    w3a
    #
    @27
    w3a
    #
    @40
    @29
    @18
    @41
    @11
    @27
    @29
    @15
    @6
    @16
    @17
    @29
    @12
    @3
    @14
    @5
    cR
    cP
    cA
    eleq1
    @29
    @13
    @4
    cR
    cP
    cW
    c.le
    breq1
    notbid
    anbi12d
    3anbi1d
    3anbi2d
    @42
    @35
    cQ
    @39
    @42
    @2
    @6
    @7
    @16
    @22
    @35
    cQ
    wceq
    @2
    @6
    @10
    @41
    @27
    simp11
    #
    @11
    @6
    @16
    @17
    @27
    simp21
    #
    @7
    @9
    @2
    @6
    @41
    @27
    simp13l
    #
    @11
    @6
    @16
    @17
    @27
    simp22
    @21
    @22
    @23
    @19
    @26
    @11
    @41
    simp322
    cA
    cP
    cQ
    cS
    cU
    cF
    @35
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme18d.l
    cdleme18d.j
    cdleme18d.m
    cdleme18d.a
    cdleme18d.h
    cdleme18d.u
    cdleme18d.f
    @35
    eqid
    cdleme17d1
    syl131anc
    @42
    @2
    @6
    @7
    @17
    @23
    @39
    cQ
    wceq
    @43
    @44
    @45
    @11
    @6
    @16
    @17
    @27
    simp23
    @21
    @22
    @23
    @19
    @26
    @11
    @41
    simp323
    cA
    cP
    cQ
    cT
    cU
    cD
    @39
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme18d.l
    cdleme18d.j
    cdleme18d.m
    cdleme18d.a
    cdleme18d.h
    cdleme18d.u
    cdleme18d.d
    @39
    eqid
    cdleme17d1
    syl131anc
    eqtr4d
    syl6bi
    @30
    @20
    cF
    cR
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
    #
    @20
    cD
    cR
    cT
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
    wceq
    #
    @29
    @40
    cG
    @49
    cE
    @53
    cdleme18d.g
    cdleme18d.e
    eqeq12i
    #
    @29
    @49
    @35
    @53
    @39
    @29
    @48
    @34
    @20
    c.an
    @29
    @47
    @33
    cF
    c.or
    @29
    @46
    @32
    cW
    c.an
    cR
    cP
    cS
    c.or
    oveq1
    oveq1d
    oveq2d
    oveq2d
    @29
    @52
    @38
    @20
    c.an
    @29
    @51
    @37
    cD
    c.or
    @29
    @50
    @36
    cW
    c.an
    cR
    cP
    cT
    c.or
    oveq1
    oveq1d
    oveq2d
    oveq2d
    eqeq12d
    syl5bb
    sylibrd
    com12
    @31
    @28
    @30
    @31
    @28
    @20
    cF
    cQ
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
    #
    @20
    cD
    cQ
    cT
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
    wceq
    #
    @30
    @31
    @28
    @11
    @10
    @16
    @17
    w3a
    #
    @19
    cQ
    @20
    c.le
    wbr
    #
    @22
    @23
    w3a
    #
    @26
    w3a
    #
    w3a
    #
    @64
    @31
    @18
    @65
    @27
    @68
    @11
    @31
    @15
    @10
    @16
    @17
    @31
    @12
    @7
    @14
    @9
    cR
    cQ
    cA
    eleq1
    @31
    @13
    @8
    cR
    cQ
    cW
    c.le
    breq1
    notbid
    anbi12d
    3anbi1d
    @31
    @24
    @67
    @19
    @26
    @31
    @21
    @66
    @22
    @23
    cR
    cQ
    @20
    c.le
    breq1
    3anbi1d
    3anbi2d
    3anbi23d
    @69
    @59
    cP
    @63
    @69
    @0
    @1
    @6
    @10
    @16
    @19
    @22
    @26
    @59
    cP
    wceq
    @0
    @1
    @6
    @10
    @65
    @68
    simp11l
    #
    @0
    @1
    @6
    @10
    @65
    @68
    simp11r
    #
    @2
    @6
    @10
    @65
    @68
    simp12
    #
    @11
    @10
    @16
    @17
    @68
    simp21
    #
    @11
    @10
    @16
    @17
    @68
    simp22
    @11
    @65
    @19
    @67
    @26
    simp31
    #
    @66
    @22
    @23
    @19
    @26
    @11
    @65
    simp322
    @11
    @65
    @19
    @67
    @26
    simp33
    #
    cA
    cP
    cQ
    cS
    cU
    cF
    @59
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vr
    cdleme18d.l
    cdleme18d.j
    cdleme18d.m
    cdleme18d.a
    cdleme18d.h
    cdleme18d.u
    cdleme18d.f
    @59
    eqid
    cdleme18c
    syl233anc
    @69
    @0
    @1
    @6
    @10
    @17
    @19
    @23
    @26
    @63
    cP
    wceq
    @70
    @71
    @72
    @73
    @11
    @10
    @16
    @17
    @68
    simp23
    @74
    @66
    @22
    @23
    @19
    @26
    @11
    @65
    simp323
    @75
    cA
    cP
    cQ
    cT
    cU
    cD
    @63
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vr
    cdleme18d.l
    cdleme18d.j
    cdleme18d.m
    cdleme18d.a
    cdleme18d.h
    cdleme18d.u
    cdleme18d.d
    @63
    eqid
    cdleme18c
    syl233anc
    eqtr4d
    syl6bi
    @30
    @54
    @31
    @64
    @55
    @31
    @49
    @59
    @53
    @63
    @31
    @48
    @58
    @20
    c.an
    @31
    @47
    @57
    cF
    c.or
    @31
    @46
    @56
    cW
    c.an
    cR
    cQ
    cS
    c.or
    oveq1
    oveq1d
    oveq2d
    oveq2d
    @31
    @52
    @62
    @20
    c.an
    @31
    @51
    @61
    cD
    c.or
    @31
    @50
    @60
    cW
    c.an
    cR
    cQ
    cT
    c.or
    oveq1
    oveq1d
    oveq2d
    oveq2d
    eqeq12d
    syl5bb
    sylibrd
    com12
    @28
    @0
    @21
    @26
    @3
    @7
    @19
    @12
    @14
    @29
    @31
    wo
    @0
    @1
    @6
    @10
    @18
    @27
    simp11l
    @21
    @22
    @23
    @19
    @26
    @11
    @18
    simp321
    @11
    @18
    @19
    @24
    @26
    simp33
    @3
    @5
    @2
    @10
    @18
    @27
    simp12l
    @7
    @9
    @2
    @6
    @18
    @27
    simp13l
    @11
    @18
    @19
    @24
    @26
    simp31
    @12
    @14
    @16
    @17
    @11
    @27
    simp21l
    @12
    @14
    @16
    @17
    @11
    @27
    simp21r
    cA
    cP
    cQ
    cR
    c.or
    cK
    c.le
    cW
    vr
    cdleme18d.l
    cdleme18d.j
    cdleme18d.a
    cdleme0nex
    syl332anc
    mpjaod
end
