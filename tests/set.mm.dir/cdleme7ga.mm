include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cpmap.mm"
include "clines.mm"
include "cp0.mm"
include "simp11l.mm"
include "simp12l.mm"
include "simp13l.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp2r.mm"
include "simp31.mm"
include "simp33.mm"
include "cdleme3fa.mm"
include "syl132anc.mm"
include "simp2l.mm"
include "simp2rl.mm"
include "simp32.mm"
include "cdleme7b.mm"
include "syl113anc.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "linepmap.mm"
include "syl31anc.mm"
include "simp2ll.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "cdleme3.mm"
include "nbrne2.mm"
include "necomd.mm"
include "syl2anc.mm"
include "atbase.mm"
include "latmcl.mm"
include "latlej2.mm"
include "cdleme7c.mm"
include "syl323anc.mm"
include "cal.mm"
include "wb.mm"
include "hlatl.mm"
include "lhpat2.mm"
include "syl112anc.mm"
include "atncmp.mm"
include "mpbird.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "biimpd.mm"
include "mpan2d.mm"
include "breq2i.mm"
include "syl6ibr.mm"
include "mtod.mm"
include "nbrne1.mm"
include "cdleme7e.mm"
include "syl5eqner.mm"
include "2lnat.mm"
include "syl322anc.mm"
include "syl5eqel.mm"

theorem cdleme7ga
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( P =/= Q /\ R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> G e. A )

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
    #
    cS
    cW
    c.le
    wbr
    wn
    #
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
    @18
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    cG
    @18
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
    cA
    cdleme4.g
    @22
    @0
    @18
    cK
    cbs
    cfv
    #
    wcel
    #
    @25
    @27
    wcel
    #
    @18
    cK
    cpmap
    cfv
    #
    cfv
    cK
    clines
    cfv
    #
    wcel
    #
    @25
    @30
    cfv
    @31
    wcel
    #
    @18
    @25
    wne
    #
    @26
    cK
    cp0
    cfv
    #
    wne
    @26
    cA
    wcel
    @0
    @1
    @5
    @8
    @16
    @21
    simp11l
    #
    @22
    @0
    @3
    @6
    @28
    @36
    @3
    @4
    @2
    @8
    @16
    @21
    simp12l
    #
    @6
    @7
    @2
    @5
    @16
    @21
    simp13l
    #
    cA
    @27
    c.or
    cK
    cP
    cQ
    @27
    eqid
    #
    cdleme4.j
    cdleme4.a
    hlatjcl
    syl3anc
    #
    @22
    @0
    cF
    cA
    wcel
    #
    @24
    cA
    wcel
    #
    @29
    @36
    @22
    @2
    @5
    @8
    @15
    @17
    @20
    @41
    @2
    @5
    @8
    @16
    @21
    simp11
    #
    @2
    @5
    @8
    @16
    @21
    simp12
    #
    @2
    @5
    @8
    @16
    @21
    simp13
    #
    @9
    @12
    @15
    @21
    simp2r
    #
    @9
    @16
    @17
    @19
    @20
    simp31
    #
    @9
    @16
    @17
    @19
    @20
    simp33
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
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4.f
    cdleme3fa
    syl132anc
    #
    @22
    @2
    @12
    @13
    @20
    @19
    @42
    @43
    @9
    @12
    @15
    @21
    simp2l
    #
    @13
    @14
    @12
    @9
    @21
    simp2rl
    #
    @48
    @9
    @16
    @17
    @19
    @20
    simp32
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
    @24
    cW
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4.f
    cdleme4.g
    @24
    eqid
    #
    cdleme7b
    syl113anc
    #
    cA
    @27
    c.or
    cK
    cF
    @24
    @39
    cdleme4.j
    cdleme4.a
    hlatjcl
    syl3anc
    @22
    cK
    clat
    wcel
    #
    @3
    @6
    @17
    @32
    @22
    @0
    @55
    @36
    cK
    hllat
    syl
    #
    @37
    @38
    @47
    cA
    cP
    cQ
    c.or
    cK
    @30
    @31
    cdleme4.j
    cdleme4.a
    @31
    eqid
    #
    @30
    eqid
    #
    linepmap
    syl31anc
    @22
    @55
    @41
    @42
    cF
    @24
    wne
    #
    @33
    @56
    @49
    @54
    @22
    @24
    cW
    c.le
    wbr
    #
    cF
    cW
    c.le
    wbr
    wn
    #
    @59
    @22
    @55
    @23
    @27
    wcel
    #
    cW
    @27
    wcel
    #
    @60
    @56
    @22
    @0
    @10
    @13
    @62
    @36
    @10
    @11
    @15
    @9
    @21
    simp2ll
    @51
    cA
    @27
    c.or
    cK
    cR
    cS
    @39
    cdleme4.j
    cdleme4.a
    hlatjcl
    syl3anc
    #
    @22
    @1
    @63
    @0
    @1
    @5
    @8
    @16
    @21
    simp11r
    @27
    cH
    cK
    cW
    @39
    cdleme4.h
    lhpbase
    syl
    #
    @27
    cK
    c.le
    c.an
    @23
    cW
    @39
    cdleme4.l
    cdleme4.m
    latmle2
    syl3anc
    #
    @22
    @2
    @5
    @8
    @15
    @17
    @20
    @61
    @43
    @44
    @45
    @46
    @47
    @48
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
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4.f
    cdleme3
    syl132anc
    @60
    @61
    wa
    @24
    cF
    @24
    cF
    cW
    c.le
    nbrne2
    necomd
    syl2anc
    cA
    cF
    @24
    c.or
    cK
    @30
    @31
    cdleme4.j
    cdleme4.a
    @57
    @58
    linepmap
    syl31anc
    @22
    @24
    @25
    c.le
    wbr
    #
    @24
    @18
    c.le
    wbr
    #
    wn
    #
    @34
    @22
    @55
    cF
    @27
    wcel
    #
    @24
    @27
    wcel
    #
    @67
    @56
    @22
    @41
    @70
    @49
    cA
    @27
    cF
    cK
    @39
    cdleme4.a
    atbase
    syl
    @22
    @55
    @62
    @63
    @71
    @56
    @64
    @65
    @27
    cK
    c.an
    @23
    cW
    @39
    cdleme4.m
    latmcl
    syl3anc
    #
    @27
    c.or
    cK
    c.le
    cF
    @24
    @39
    cdleme4.l
    cdleme4.j
    latlej2
    syl3anc
    @22
    @68
    @24
    cU
    c.le
    wbr
    #
    @22
    @73
    wn
    #
    @24
    cU
    wne
    #
    @22
    cU
    @24
    @22
    @2
    @5
    @6
    @12
    @15
    @17
    @19
    @20
    cU
    @24
    wne
    @43
    @44
    @38
    @50
    @46
    @47
    @52
    @48
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
    @24
    cW
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4.f
    cdleme4.g
    @53
    cdleme7c
    syl323anc
    necomd
    @22
    cK
    cal
    wcel
    #
    @42
    cU
    cA
    wcel
    #
    @74
    @75
    wb
    @22
    @0
    @76
    @36
    cK
    hlatl
    syl
    @54
    @22
    @2
    @5
    @6
    @17
    @77
    @43
    @44
    @38
    @47
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
    @24
    cU
    cK
    c.le
    cdleme4.l
    cdleme4.a
    atncmp
    syl3anc
    mpbird
    @22
    @68
    @24
    @18
    cW
    c.an
    co
    #
    c.le
    wbr
    #
    @73
    @22
    @68
    @60
    @79
    @66
    @22
    @68
    @60
    wa
    #
    @79
    @22
    @55
    @71
    @28
    @63
    @80
    @79
    wb
    @56
    @72
    @40
    @65
    @27
    cK
    c.le
    c.an
    @24
    @18
    cW
    @39
    cdleme4.l
    cdleme4.m
    latlem12
    syl13anc
    biimpd
    mpan2d
    cU
    @78
    @24
    c.le
    cdleme4.u
    breq2i
    syl6ibr
    mtod
    @67
    @69
    wa
    @25
    @18
    @24
    @25
    @18
    c.le
    nbrne1
    necomd
    syl2anc
    @22
    @26
    cG
    @35
    cdleme4.g
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
    @24
    cW
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4.f
    cdleme4.g
    @53
    cdleme7e
    syl5eqner
    cA
    @27
    @30
    cK
    c.an
    @31
    @18
    @25
    @35
    @39
    cdleme4.m
    @35
    eqid
    cdleme4.a
    @57
    @58
    2lnat
    syl322anc
    syl5eqel
end
