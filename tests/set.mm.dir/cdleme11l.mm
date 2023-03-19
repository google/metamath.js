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
include "simp21.mm"
include "simp22l.mm"
include "simp23l.mm"
include "simp23r.mm"
include "simp31.mm"
include "simp33.mm"
include "eqid.mm"
include "cdleme11e.mm"
include "syl333anc.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "adantl.mm"
include "simp13.mm"
include "cdleme11k.mm"
include "syl132anc.mm"
include "adantr.mm"
include "simp22.mm"
include "simp32.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"

theorem cdleme11l
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ S =/= T ) ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ U .<_ ( S .\/ T ) ) ) -> F =/= G )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
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
    @14
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
    #
    w3a
    #
    w3a
    #
    cP
    cS
    c.or
    co
    cW
    c.an
    co
    #
    cP
    cT
    c.or
    co
    cW
    c.an
    co
    #
    wne
    #
    cF
    cG
    wne
    @19
    @0
    @1
    @2
    @6
    @7
    @10
    @11
    @15
    @17
    @22
    @0
    @1
    @4
    @13
    @18
    simp11
    #
    @0
    @1
    @4
    @13
    @18
    simp12
    #
    @2
    @3
    @0
    @1
    @13
    @18
    simp13l
    @5
    @6
    @9
    @12
    @18
    simp21
    #
    @7
    @8
    @6
    @12
    @5
    @18
    simp22l
    @10
    @11
    @6
    @9
    @5
    @18
    simp23l
    #
    @10
    @11
    @6
    @9
    @5
    @18
    simp23r
    @5
    @13
    @15
    @16
    @17
    simp31
    #
    @5
    @13
    @15
    @16
    @17
    simp33
    cA
    @20
    @21
    cP
    cQ
    cS
    cT
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
    @20
    eqid
    #
    @21
    eqid
    #
    cdleme11e
    syl333anc
    @19
    cF
    cG
    @20
    @21
    @19
    cF
    cG
    wceq
    #
    @20
    @21
    wceq
    @19
    @30
    wa
    cQ
    cF
    c.or
    co
    #
    cW
    c.an
    co
    #
    cQ
    cG
    c.or
    co
    #
    cW
    c.an
    co
    #
    @20
    @21
    @30
    @32
    @34
    wceq
    @19
    @30
    @31
    @33
    cW
    c.an
    cF
    cG
    cQ
    c.or
    oveq2
    oveq1d
    adantl
    @19
    @20
    @32
    wceq
    #
    @30
    @19
    @0
    @1
    @4
    @6
    @10
    @15
    @35
    @23
    @24
    @0
    @1
    @4
    @13
    @18
    simp13
    #
    @25
    @26
    @27
    cA
    @20
    cU
    cP
    cQ
    cS
    cQ
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
    @28
    cdleme12.u
    cdleme12.f
    cdleme11k
    syl132anc
    adantr
    @19
    @21
    @34
    wceq
    #
    @30
    @19
    @0
    @1
    @4
    @9
    @10
    @16
    @37
    @23
    @24
    @36
    @5
    @6
    @9
    @12
    @18
    simp22
    @26
    @5
    @13
    @15
    @16
    @17
    simp32
    cA
    @21
    cU
    cP
    cQ
    cT
    cQ
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
    @29
    cdleme12.u
    cdleme12.g
    cdleme11k
    syl132anc
    adantr
    3eqtr4d
    ex
    necon3d
    mpd
end
