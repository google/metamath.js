include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "clpl.mm"
include "cfv.mm"
include "cdleme16c.mm"
include "simp23r.mm"
include "simp33.mm"
include "wb.mm"
include "simp11l.mm"
include "simp21l.mm"
include "simp22l.mm"
include "simp11r.mm"
include "simp12l.mm"
include "simp12r.mm"
include "simp13l.mm"
include "simp23l.mm"
include "lhpat2.mm"
include "syl222anc.mm"
include "eqid.mm"
include "islpln2a.mm"
include "syl13anc.mm"
include "mpbir2and.mm"
include "eqeltrd.mm"
include "clln.mm"
include "islln2a.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "cdleme16b.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "simp31.mm"
include "cdleme3fa.mm"
include "syl132anc.mm"
include "simp22.mm"
include "simp32.mm"
include "2llnmj.mm"

theorem cdleme16d
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ S =/= T ) ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ -. U .<_ ( S .\/ T ) ) ) -> ( ( S .\/ T ) ./\ ( F .\/ G ) ) e. A )

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
    @23
    cF
    cG
    c.or
    co
    #
    c.an
    co
    cA
    wcel
    #
    @23
    @27
    c.or
    co
    #
    cK
    clpl
    cfv
    #
    wcel
    #
    @26
    @29
    @23
    cU
    c.or
    co
    #
    @30
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
    cdleme16c
    @26
    @32
    @30
    wcel
    #
    @17
    @24
    @16
    @17
    @12
    @15
    @9
    @25
    simp23r
    #
    @9
    @19
    @21
    @22
    @24
    simp33
    @26
    @0
    @10
    @13
    cU
    cA
    wcel
    #
    @33
    @17
    @24
    wa
    wb
    @0
    @1
    @5
    @8
    @19
    @25
    simp11l
    #
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
    @0
    @1
    @3
    @4
    @6
    @16
    @35
    @36
    @0
    @1
    @5
    @8
    @19
    @25
    simp11r
    @3
    @4
    @2
    @8
    @19
    @25
    simp12l
    @3
    @4
    @2
    @8
    @19
    @25
    simp12r
    @6
    @7
    @2
    @5
    @19
    @25
    simp13l
    @16
    @17
    @12
    @15
    @9
    @25
    simp23l
    #
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
    cA
    @30
    cS
    cT
    cU
    c.or
    cK
    c.le
    cdleme12.l
    cdleme12.j
    cdleme12.a
    @30
    eqid
    #
    islpln2a
    syl13anc
    mpbir2and
    eqeltrd
    @26
    @0
    @23
    cK
    clln
    cfv
    #
    wcel
    #
    @27
    @41
    wcel
    #
    @28
    @31
    wb
    @36
    @26
    @42
    @17
    @34
    @26
    @0
    @10
    @13
    @42
    @17
    wb
    @36
    @37
    @38
    cA
    cS
    cT
    c.or
    cK
    @41
    cdleme12.j
    cdleme12.a
    @41
    eqid
    #
    islln2a
    syl3anc
    mpbird
    @26
    @43
    cF
    cG
    wne
    #
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
    cdleme16b
    @26
    @0
    cF
    cA
    wcel
    #
    cG
    cA
    wcel
    #
    @43
    @45
    wb
    @36
    @26
    @2
    @5
    @8
    @12
    @16
    @21
    @46
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
    @9
    @12
    @15
    @18
    @25
    simp21
    @39
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
    @47
    @48
    @49
    @50
    @9
    @12
    @15
    @18
    @25
    simp22
    @39
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
    cF
    cG
    c.or
    cK
    @41
    cdleme12.j
    cdleme12.a
    @44
    islln2a
    syl3anc
    mpbird
    cA
    @30
    c.or
    cK
    c.an
    @41
    @23
    @27
    cdleme12.j
    cdleme12.m
    cdleme12.a
    @44
    @40
    2llnmj
    syl3anc
    mpbird
end
