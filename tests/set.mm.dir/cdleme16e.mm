include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp21l.mm"
include "simp22l.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "simp23l.mm"
include "simp31.mm"
include "cdleme3fa.mm"
include "syl132anc.mm"
include "simp22.mm"
include "simp32.mm"
include "latmle1.mm"
include "cdleme15.mm"
include "wb.mm"
include "latmcl.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cal.mm"
include "hlatl.mm"
include "cdleme16d.mm"
include "simp21r.mm"
include "simp23r.mm"
include "lhpat.mm"
include "syl222anc.mm"
include "atcmp.mm"
include "mpbid.mm"

theorem cdleme16e
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ S =/= T ) ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ -. U .<_ ( S .\/ T ) ) ) -> ( ( S .\/ T ) ./\ ( F .\/ G ) ) = ( ( S .\/ T ) ./\ W ) )

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
    cQ
    cW
    c.le
    wbr
    wn
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
    @16
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
    @19
    cF
    cG
    c.or
    co
    #
    c.an
    co
    #
    @19
    cW
    c.an
    co
    #
    c.le
    wbr
    #
    @24
    @25
    wceq
    #
    @22
    @24
    @19
    c.le
    wbr
    #
    @24
    cW
    c.le
    wbr
    #
    @26
    @22
    cK
    clat
    wcel
    #
    @19
    cK
    cbs
    cfv
    #
    wcel
    #
    @23
    @31
    wcel
    #
    @28
    @22
    @0
    @30
    @0
    @1
    @3
    @4
    @15
    @21
    simp11l
    #
    cK
    hllat
    syl
    #
    @22
    @0
    @6
    @9
    @32
    @34
    @6
    @7
    @11
    @14
    @5
    @21
    simp21l
    #
    @9
    @10
    @8
    @14
    @5
    @21
    simp22l
    #
    cA
    @31
    c.or
    cK
    cS
    cT
    @31
    eqid
    #
    cdleme12.j
    cdleme12.a
    hlatjcl
    syl3anc
    #
    @22
    @0
    cF
    cA
    wcel
    #
    cG
    cA
    wcel
    #
    @33
    @34
    @22
    @2
    @3
    @4
    @8
    @12
    @17
    @40
    @2
    @3
    @4
    @15
    @21
    simp11
    #
    @2
    @3
    @4
    @15
    @21
    simp12
    #
    @2
    @3
    @4
    @15
    @21
    simp13
    #
    @5
    @8
    @11
    @14
    @21
    simp21
    @12
    @13
    @8
    @11
    @5
    @21
    simp23l
    #
    @5
    @15
    @17
    @18
    @20
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
    @22
    @2
    @3
    @4
    @11
    @12
    @18
    @41
    @42
    @43
    @44
    @5
    @8
    @11
    @14
    @21
    simp22
    @45
    @5
    @15
    @17
    @18
    @20
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
    @31
    c.or
    cK
    cF
    cG
    @38
    cdleme12.j
    cdleme12.a
    hlatjcl
    syl3anc
    #
    @31
    cK
    c.le
    c.an
    @19
    @23
    @38
    cdleme12.l
    cdleme12.m
    latmle1
    syl3anc
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
    cdleme15
    @22
    @30
    @24
    @31
    wcel
    #
    @32
    cW
    @31
    wcel
    #
    @28
    @29
    wa
    @26
    wb
    @35
    @22
    @30
    @32
    @33
    @47
    @35
    @39
    @46
    @31
    cK
    c.an
    @19
    @23
    @38
    cdleme12.m
    latmcl
    syl3anc
    @39
    @22
    @1
    @48
    @0
    @1
    @3
    @4
    @15
    @21
    simp11r
    #
    @31
    cH
    cK
    cW
    @38
    cdleme12.h
    lhpbase
    syl
    @31
    cK
    c.le
    c.an
    @24
    @19
    cW
    @38
    cdleme12.l
    cdleme12.m
    latlem12
    syl13anc
    mpbi2and
    @22
    cK
    cal
    wcel
    #
    @24
    cA
    wcel
    @25
    cA
    wcel
    #
    @26
    @27
    wb
    @22
    @0
    @50
    @34
    cK
    hlatl
    syl
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
    cdleme16d
    @22
    @0
    @1
    @6
    @7
    @9
    @13
    @51
    @34
    @49
    @36
    @6
    @7
    @11
    @14
    @5
    @21
    simp21r
    @37
    @12
    @13
    @8
    @11
    @5
    @21
    simp23r
    cA
    cS
    cT
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
    lhpat
    syl222anc
    cA
    @24
    @25
    cK
    c.le
    cdleme12.l
    cdleme12.a
    atcmp
    syl3anc
    mpbid
end
