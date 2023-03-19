include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13l.mm"
include "simp23l.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23r.mm"
include "simp33.mm"
include "jca.mm"
include "cdleme13.mm"
include "syl133anc.mm"
include "wi.mm"
include "simp11l.mm"
include "simp21l.mm"
include "simp22l.mm"
include "simp12l.mm"
include "simp13.mm"
include "simp31.mm"
include "cdleme3fa.mm"
include "syl132anc.mm"
include "simp32.mm"
include "dalaw.mm"
include "mpd.mm"

theorem cdleme14
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ S =/= T ) ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ -. U .<_ ( S .\/ T ) ) ) -> ( ( S .\/ T ) ./\ ( F .\/ G ) ) .<_ ( ( ( T .\/ P ) ./\ ( G .\/ Q ) ) .\/ ( ( P .\/ S ) ./\ ( Q .\/ F ) ) ) )

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
    cT
    cG
    c.or
    co
    c.an
    co
    @20
    c.le
    wbr
    #
    @23
    cF
    cG
    c.or
    co
    c.an
    co
    cT
    cP
    c.or
    co
    cG
    cQ
    c.or
    co
    c.an
    co
    cP
    cS
    c.or
    co
    cQ
    cF
    c.or
    co
    c.an
    co
    c.or
    co
    c.le
    wbr
    #
    @26
    @2
    @5
    @6
    @16
    @12
    @15
    @17
    @24
    wa
    @27
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
    @6
    @7
    @2
    @5
    @19
    @25
    simp13l
    #
    @16
    @17
    @12
    @15
    @9
    @25
    simp23l
    #
    @9
    @12
    @15
    @18
    @25
    simp21
    #
    @9
    @12
    @15
    @18
    @25
    simp22
    #
    @26
    @17
    @24
    @16
    @17
    @12
    @15
    @9
    @25
    simp23r
    @9
    @19
    @21
    @22
    @24
    simp33
    jca
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
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme12.u
    cdleme12.f
    cdleme12.g
    cdleme13
    syl133anc
    @26
    @0
    @10
    @13
    @3
    cF
    cA
    wcel
    #
    cG
    cA
    wcel
    #
    @6
    @27
    @28
    wi
    @0
    @1
    @5
    @8
    @19
    @25
    simp11l
    @10
    @11
    @15
    @18
    @9
    @25
    simp21l
    @13
    @14
    @12
    @18
    @9
    @25
    simp22l
    @3
    @4
    @2
    @8
    @19
    @25
    simp12l
    @26
    @2
    @5
    @8
    @12
    @16
    @21
    @35
    @29
    @30
    @2
    @5
    @8
    @19
    @25
    simp13
    #
    @33
    @32
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
    @36
    @29
    @30
    @37
    @34
    @32
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
    @31
    cA
    cS
    cT
    cP
    cF
    cG
    cQ
    c.or
    cK
    c.le
    c.an
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    dalaw
    syl133anc
    mpd
end
