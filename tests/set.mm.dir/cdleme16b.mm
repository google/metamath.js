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
include "simp13.mm"
include "simp21.mm"
include "simp23l.mm"
include "simp31.mm"
include "eqid.mm"
include "cdleme3g.mm"
include "syl132anc.mm"
include "wceq.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp21l.mm"
include "cdleme3fa.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp22l.mm"
include "atbase.mm"
include "latmcl.mm"
include "latlej2.mm"
include "adantr.mm"
include "hlatlej2.mm"
include "atmod2i1.mm"
include "syl131anc.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "sylan9eq.mm"
include "simp11r.mm"
include "simp13l.mm"
include "simp22.mm"
include "simp23r.mm"
include "simp33.mm"
include "jca.mm"
include "cdleme12.mm"
include "syl233anc.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "ex.mm"
include "cal.mm"
include "wb.mm"
include "hlatl.mm"
include "simp12l.mm"
include "simp12r.mm"
include "lhpat2.mm"
include "syl222anc.mm"
include "atcmp.mm"
include "sylibd.mm"
include "necon3d.mm"
include "mpd.mm"

theorem cdleme16b
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ S =/= T ) ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ -. U .<_ ( S .\/ T ) ) ) -> F =/= G )

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
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    cF
    cU
    wne
    #
    cF
    cG
    wne
    @25
    @2
    @5
    @8
    @12
    @16
    @21
    @26
    @2
    @5
    @8
    @19
    @24
    simp11
    #
    @2
    @5
    @8
    @19
    @24
    simp12
    #
    @2
    @5
    @8
    @19
    @24
    simp13
    #
    @9
    @12
    @15
    @18
    @24
    simp21
    #
    @16
    @17
    @12
    @15
    @9
    @24
    simp23l
    #
    @9
    @19
    @21
    @22
    @23
    simp31
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
    cP
    cS
    c.or
    co
    cW
    c.an
    co
    #
    cW
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme12.u
    cdleme12.f
    @33
    eqid
    cdleme3g
    syl132anc
    @25
    cF
    cG
    cF
    cU
    @25
    cF
    cG
    wceq
    #
    cF
    cU
    c.le
    wbr
    #
    cF
    cU
    wceq
    #
    @25
    @34
    @35
    @25
    @34
    wa
    #
    cF
    cS
    cF
    c.or
    co
    #
    cT
    c.an
    co
    #
    cF
    c.or
    co
    #
    cU
    c.le
    @25
    cF
    @40
    c.le
    wbr
    #
    @34
    @25
    cK
    clat
    wcel
    #
    @39
    cK
    cbs
    cfv
    #
    wcel
    #
    cF
    @43
    wcel
    #
    @41
    @25
    @0
    @42
    @0
    @1
    @5
    @8
    @19
    @24
    simp11l
    #
    cK
    hllat
    syl
    #
    @25
    @42
    @38
    @43
    wcel
    #
    cT
    @43
    wcel
    #
    @44
    @47
    @25
    @0
    @10
    cF
    cA
    wcel
    #
    @48
    @46
    @10
    @11
    @15
    @18
    @9
    @24
    simp21l
    #
    @25
    @2
    @5
    @8
    @12
    @16
    @21
    @50
    @27
    @28
    @29
    @30
    @31
    @32
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
    #
    cA
    @43
    c.or
    cK
    cS
    cF
    @43
    eqid
    #
    cdleme12.j
    cdleme12.a
    hlatjcl
    syl3anc
    #
    @25
    @13
    @49
    @13
    @14
    @12
    @18
    @9
    @24
    simp22l
    cA
    @43
    cT
    cK
    @53
    cdleme12.a
    atbase
    syl
    #
    @43
    cK
    c.an
    @38
    cT
    @53
    cdleme12.m
    latmcl
    syl3anc
    @25
    @50
    @45
    @52
    cA
    @43
    cF
    cK
    @53
    cdleme12.a
    atbase
    syl
    @43
    c.or
    cK
    c.le
    @39
    cF
    @53
    cdleme12.l
    cdleme12.j
    latlej2
    syl3anc
    adantr
    @37
    @40
    @38
    cT
    cG
    c.or
    co
    #
    c.an
    co
    #
    cU
    @25
    @34
    @40
    @38
    cT
    cF
    c.or
    co
    #
    c.an
    co
    #
    @57
    @25
    @0
    @50
    @48
    @49
    cF
    @38
    c.le
    wbr
    #
    @40
    @59
    wceq
    @46
    @52
    @54
    @55
    @25
    @0
    @10
    @50
    @60
    @46
    @51
    @52
    cA
    cS
    cF
    c.or
    cK
    c.le
    cdleme12.l
    cdleme12.j
    cdleme12.a
    hlatlej2
    syl3anc
    cA
    @43
    cF
    c.or
    cK
    c.le
    c.an
    @38
    cT
    @53
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    atmod2i1
    syl131anc
    @34
    @58
    @56
    @38
    c.an
    cF
    cG
    cT
    c.or
    oveq2
    oveq2d
    sylan9eq
    @25
    @57
    cU
    wceq
    #
    @34
    @25
    @0
    @1
    @5
    @6
    @16
    @12
    @15
    @17
    @23
    wa
    @61
    @46
    @0
    @1
    @5
    @8
    @19
    @24
    simp11r
    #
    @28
    @6
    @7
    @2
    @5
    @19
    @24
    simp13l
    #
    @31
    @30
    @9
    @12
    @15
    @18
    @24
    simp22
    @25
    @17
    @23
    @16
    @17
    @12
    @15
    @9
    @24
    simp23r
    @9
    @19
    @21
    @22
    @23
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
    cdleme12
    syl233anc
    adantr
    eqtrd
    breqtrd
    ex
    @25
    cK
    cal
    wcel
    #
    @50
    cU
    cA
    wcel
    #
    @35
    @36
    wb
    @25
    @0
    @64
    @46
    cK
    hlatl
    syl
    @52
    @25
    @0
    @1
    @3
    @4
    @6
    @16
    @65
    @46
    @62
    @3
    @4
    @2
    @8
    @19
    @24
    simp12l
    @3
    @4
    @2
    @8
    @19
    @24
    simp12r
    @63
    @31
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
    cF
    cU
    cK
    c.le
    cdleme12.l
    cdleme12.a
    atcmp
    syl3anc
    sylibd
    necon3d
    mpd
end
