include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "simp21l.mm"
include "simp22.mm"
include "simp31.mm"
include "cdleme1.mm"
include "syl13anc.mm"
include "simp1l.mm"
include "simp21.mm"
include "simp23.mm"
include "lhpat2.mm"
include "syl112anc.mm"
include "simp31l.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "eqtr4d.mm"
include "simp32.mm"
include "simp32l.mm"
include "oveq12d.mm"
include "simp33.mm"
include "2llnma2.mm"
include "syl131anc.mm"
include "eqtrd.mm"

theorem cdleme12
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ Q e. A /\ P =/= Q ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( S =/= T /\ -. U .<_ ( S .\/ T ) ) ) ) -> ( ( S .\/ F ) ./\ ( T .\/ G ) ) = U )

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
    cP
    cQ
    wne
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
    cS
    cT
    wne
    cU
    cS
    cT
    c.or
    co
    c.le
    wbr
    wn
    wa
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
    c.an
    co
    cU
    cS
    c.or
    co
    #
    cU
    cT
    c.or
    co
    #
    c.an
    co
    #
    cU
    @17
    @18
    @20
    @19
    @21
    c.an
    @17
    @18
    cS
    cU
    c.or
    co
    #
    @20
    @17
    @2
    @3
    @6
    @11
    @18
    @23
    wceq
    @2
    @8
    @16
    simp1
    #
    @3
    @4
    @6
    @7
    @2
    @16
    simp21l
    #
    @2
    @5
    @6
    @7
    @16
    simp22
    #
    @2
    @8
    @11
    @14
    @15
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
    cdleme1
    syl13anc
    @17
    @0
    cU
    cA
    wcel
    #
    @9
    @20
    @23
    wceq
    @0
    @1
    @8
    @16
    simp1l
    #
    @17
    @2
    @5
    @6
    @7
    @27
    @24
    @2
    @5
    @6
    @7
    @16
    simp21
    @26
    @2
    @5
    @6
    @7
    @16
    simp23
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
    syl112anc
    #
    @9
    @10
    @14
    @15
    @2
    @8
    simp31l
    #
    cA
    c.or
    cK
    cU
    cS
    cdleme12.j
    cdleme12.a
    hlatjcom
    syl3anc
    eqtr4d
    @17
    @19
    cT
    cU
    c.or
    co
    #
    @21
    @17
    @2
    @3
    @6
    @14
    @19
    @31
    wceq
    @24
    @25
    @26
    @2
    @8
    @11
    @14
    @15
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
    cdleme1
    syl13anc
    @17
    @0
    @27
    @12
    @21
    @31
    wceq
    @28
    @29
    @12
    @13
    @11
    @15
    @2
    @8
    simp32l
    #
    cA
    c.or
    cK
    cU
    cT
    cdleme12.j
    cdleme12.a
    hlatjcom
    syl3anc
    eqtr4d
    oveq12d
    @17
    @0
    @9
    @12
    @27
    @15
    @22
    cU
    wceq
    @28
    @30
    @32
    @29
    @2
    @8
    @11
    @14
    @15
    simp33
    cA
    cS
    cT
    cU
    c.or
    cK
    c.le
    c.an
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    2llnma2
    syl131anc
    eqtrd
end
