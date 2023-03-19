include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "simp11l.mm"
include "simp11r.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simp21.mm"
include "cdleme1.mm"
include "syl23anc.mm"
include "simp22.mm"
include "oveq12d.mm"
include "simp21l.mm"
include "simp22l.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp23l.mm"
include "simp31.mm"
include "cdleme3fa.mm"
include "syl132anc.mm"
include "simp32.mm"
include "hlatj4.mm"
include "syl122anc.mm"
include "simp12r.mm"
include "lhpat2.mm"
include "syl222anc.mm"
include "hlatjidm.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "3eqtr4d.mm"

theorem cdleme16c
  let cA: class A
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
  assume cdleme12.l: |- .<_ = ( le ` K )
  assume cdleme12.j: |- .\/ = ( join ` K )
  assume cdleme12.m: |- ./\ = ( meet ` K )
  assume cdleme12.a: |- A = ( Atoms ` K )
  assume cdleme12.h: |- H = ( LHyp ` K )
  assume cdleme12.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme12.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme12.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ S =/= T ) ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ -. U .<_ ( S .\/ T ) ) ) -> ( ( S .\/ T ) .\/ ( F .\/ G ) ) = ( ( S .\/ T ) .\/ U ) )

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
    wn
    #
    cT
    @20
    c.le
    wbr
    wn
    #
    cU
    cS
    cT
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    cS
    cF
    c.or
    co
    #
    cT
    cG
    c.or
    co
    #
    c.or
    co
    #
    cS
    cU
    c.or
    co
    #
    cT
    cU
    c.or
    co
    #
    c.or
    co
    #
    @23
    cF
    cG
    c.or
    co
    c.or
    co
    #
    @23
    cU
    c.or
    co
    #
    @26
    @27
    @30
    @28
    @31
    c.or
    @26
    @0
    @1
    @3
    @6
    @12
    @27
    @30
    wceq
    @0
    @1
    @5
    @8
    @19
    @25
    simp11l
    #
    @0
    @1
    @5
    @8
    @19
    @25
    simp11r
    #
    @3
    @4
    @2
    @8
    @19
    @25
    simp12l
    #
    @6
    @7
    @2
    @5
    @19
    @25
    simp13l
    #
    @9
    @12
    @15
    @18
    @25
    simp21
    #
    cA
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
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme12.u
    cdleme12.f
    cdleme1
    syl23anc
    @26
    @0
    @1
    @3
    @6
    @15
    @28
    @31
    wceq
    @35
    @36
    @37
    @38
    @9
    @12
    @15
    @18
    @25
    simp22
    #
    cA
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
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme12.u
    cdleme12.g
    cdleme1
    syl23anc
    oveq12d
    @26
    @0
    @10
    @13
    cF
    cA
    wcel
    #
    cG
    cA
    wcel
    #
    @33
    @29
    wceq
    @35
    @10
    @11
    @15
    @18
    @9
    @25
    simp21l
    #
    @13
    @14
    @12
    @18
    @9
    @25
    simp22l
    #
    @26
    @2
    @5
    @8
    @12
    @16
    @21
    @41
    @2
    @5
    @8
    @19
    @25
    simp11
    #
    @2
    @5
    @8
    @19
    @25
    simp12
    #
    @2
    @5
    @8
    @19
    @25
    simp13
    #
    @39
    @16
    @17
    @12
    @15
    @9
    @25
    simp23l
    #
    @9
    @19
    @21
    @22
    @24
    simp31
    cA
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
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme12.u
    cdleme12.f
    cdleme3fa
    syl132anc
    @26
    @2
    @5
    @8
    @15
    @16
    @22
    @42
    @45
    @46
    @47
    @40
    @48
    @9
    @19
    @21
    @22
    @24
    simp32
    cA
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
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme12.u
    cdleme12.g
    cdleme3fa
    syl132anc
    cA
    cS
    cT
    cF
    cG
    c.or
    cK
    cdleme12.j
    cdleme12.a
    hlatj4
    syl122anc
    @26
    @23
    cU
    cU
    c.or
    co
    #
    c.or
    co
    #
    @34
    @32
    @26
    @49
    cU
    @23
    c.or
    @26
    @0
    cU
    cA
    wcel
    #
    @49
    cU
    wceq
    @35
    @26
    @0
    @1
    @3
    @4
    @6
    @16
    @51
    @35
    @36
    @37
    @3
    @4
    @2
    @8
    @19
    @25
    simp12r
    @38
    @48
    cA
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme12.u
    lhpat2
    syl222anc
    #
    cA
    c.or
    cK
    cU
    cdleme12.j
    cdleme12.a
    hlatjidm
    syl2anc
    oveq2d
    @26
    @0
    @10
    @13
    @51
    @51
    @50
    @32
    wceq
    @35
    @43
    @44
    @52
    @52
    cA
    cS
    cT
    cU
    cU
    c.or
    cK
    cdleme12.j
    cdleme12.a
    hlatj4
    syl122anc
    eqtr3d
    3eqtr4d
end
