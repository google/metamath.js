include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "eqid.mm"
include "cdleme7d.mm"
include "wceq.mm"
include "simp11l.mm"
include "simp2ll.mm"
include "cdleme7ga.mm"
include "hlatlej2.mm"
include "syl3anc.mm"
include "biantrurd.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "hlatjcl.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "simp11.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp32.mm"
include "cdleme6.mm"
include "syl132anc.mm"
include "breq2d.mm"
include "bitrd.mm"
include "cal.mm"
include "hlatl.mm"
include "simp12.mm"
include "simp31.mm"
include "lhpat2.mm"
include "syl112anc.mm"
include "atcmp.mm"
include "3bitrd.mm"
include "necon3bbid.mm"
include "mpbird.mm"

theorem cdleme7
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme4.l: |- .<_ = ( le ` K )
  assume cdleme4.j: |- .\/ = ( join ` K )
  assume cdleme4.m: |- ./\ = ( meet ` K )
  assume cdleme4.a: |- A = ( Atoms ` K )
  assume cdleme4.h: |- H = ( LHyp ` K )
  assume cdleme4.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme4.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme4.g: |- G = ( ( P .\/ Q ) ./\ ( F .\/ ( ( R .\/ S ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( P =/= Q /\ R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> -. G .<_ W )

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
    wa
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
    @16
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    cG
    cW
    c.le
    wbr
    #
    wn
    cG
    cU
    wne
    cA
    cP
    cQ
    cR
    cS
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cR
    cS
    c.or
    co
    cW
    c.an
    co
    #
    cW
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4.f
    cdleme4.g
    @22
    eqid
    cdleme7d
    @20
    @21
    cG
    cU
    @20
    @21
    cG
    cR
    cG
    c.or
    co
    #
    c.le
    wbr
    #
    @21
    wa
    #
    cG
    cU
    c.le
    wbr
    #
    cG
    cU
    wceq
    #
    @20
    @24
    @21
    @20
    @0
    @10
    cG
    cA
    wcel
    #
    @24
    @0
    @1
    @5
    @8
    @14
    @19
    simp11l
    #
    @10
    @11
    @13
    @9
    @19
    simp2ll
    #
    cA
    cP
    cQ
    cR
    cS
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4.f
    cdleme4.g
    cdleme7ga
    #
    cA
    cR
    cG
    c.or
    cK
    c.le
    cdleme4.l
    cdleme4.j
    cdleme4.a
    hlatlej2
    syl3anc
    biantrurd
    @20
    @25
    cG
    @23
    cW
    c.an
    co
    #
    c.le
    wbr
    #
    @26
    @20
    cK
    clat
    wcel
    #
    cG
    cK
    cbs
    cfv
    #
    wcel
    #
    @23
    @35
    wcel
    #
    cW
    @35
    wcel
    #
    @25
    @33
    wb
    @20
    @0
    @34
    @29
    cK
    hllat
    syl
    @20
    @28
    @36
    @31
    cA
    @35
    cG
    cK
    @35
    eqid
    #
    cdleme4.a
    atbase
    syl
    @20
    @0
    @10
    @28
    @37
    @29
    @30
    @31
    cA
    @35
    c.or
    cK
    cR
    cG
    @39
    cdleme4.j
    cdleme4.a
    hlatjcl
    syl3anc
    @20
    @1
    @38
    @0
    @1
    @5
    @8
    @14
    @19
    simp11r
    @35
    cH
    cK
    cW
    @39
    cdleme4.h
    lhpbase
    syl
    @35
    cK
    c.le
    c.an
    cG
    @23
    cW
    @39
    cdleme4.l
    cdleme4.m
    latlem12
    syl13anc
    @20
    @32
    cU
    cG
    c.le
    @20
    @2
    @3
    @6
    @12
    @13
    @17
    @32
    cU
    wceq
    @2
    @5
    @8
    @14
    @19
    simp11
    #
    @3
    @4
    @2
    @8
    @14
    @19
    simp12l
    @6
    @7
    @2
    @5
    @14
    @19
    simp13l
    #
    @9
    @12
    @13
    @19
    simp2l
    @9
    @12
    @13
    @19
    simp2r
    @9
    @14
    @15
    @17
    @18
    simp32
    cA
    cP
    cQ
    cR
    cS
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4.f
    cdleme4.g
    cdleme6
    syl132anc
    breq2d
    bitrd
    @20
    cK
    cal
    wcel
    #
    @28
    cU
    cA
    wcel
    #
    @26
    @27
    wb
    @20
    @0
    @42
    @29
    cK
    hlatl
    syl
    @31
    @20
    @2
    @5
    @6
    @15
    @43
    @40
    @2
    @5
    @8
    @14
    @19
    simp12
    @41
    @9
    @14
    @15
    @17
    @18
    simp31
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
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    lhpat2
    syl112anc
    cA
    cG
    cU
    cK
    c.le
    cdleme4.l
    cdleme4.a
    atcmp
    syl3anc
    3bitrd
    necon3bbid
    mpbird
end
