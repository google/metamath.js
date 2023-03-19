include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cdleme7a.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
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
include "latmle2.mm"
include "syl5eqbr.mm"
include "cdleme3.mm"
include "wi.mm"
include "lhpat2.mm"
include "syl112anc.mm"
include "simp2.mm"
include "simp3.mm"
include "cdleme7c.mm"
include "syl311anc.mm"
include "hlatexch2.mm"
include "syl131anc.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "simp2ll.mm"
include "wb.mm"
include "atbase.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "lattr.mm"
include "mpan2d.mm"
include "syld.mm"
include "mtod.mm"
include "nbrne2.mm"
include "syl2anc.mm"

theorem cdleme7d
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
  let cV: class V
  let cW: class W
  assume cdleme4.l: |- .<_ = ( le ` K )
  assume cdleme4.j: |- .\/ = ( join ` K )
  assume cdleme4.m: |- ./\ = ( meet ` K )
  assume cdleme4.a: |- A = ( Atoms ` K )
  assume cdleme4.h: |- H = ( LHyp ` K )
  assume cdleme4.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme4.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme4.g: |- G = ( ( P .\/ Q ) ./\ ( F .\/ ( ( R .\/ S ) ./\ W ) ) )
  assume cdleme7.v: |- V = ( ( R .\/ S ) ./\ W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( P =/= Q /\ R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> G =/= U )

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
    cF
    cV
    c.or
    co
    #
    c.le
    wbr
    cU
    @23
    c.le
    wbr
    #
    wn
    cG
    cU
    wne
    @22
    cG
    @18
    @23
    c.an
    co
    #
    @23
    c.le
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
    cV
    cW
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4.f
    cdleme4.g
    cdleme7.v
    cdleme7a
    @22
    cK
    clat
    wcel
    #
    @18
    cK
    cbs
    cfv
    #
    wcel
    #
    @23
    @27
    wcel
    #
    @25
    @23
    c.le
    wbr
    @22
    @0
    @26
    @0
    @1
    @5
    @8
    @16
    @21
    simp11l
    #
    cK
    hllat
    syl
    #
    @22
    @0
    @3
    @6
    @28
    @30
    @3
    @4
    @2
    @8
    @16
    @21
    simp12l
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
    cV
    cA
    wcel
    #
    @29
    @30
    @22
    @2
    @5
    @8
    @15
    @17
    @20
    @35
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
    @36
    @37
    @9
    @12
    @15
    @21
    simp2l
    @13
    @14
    @12
    @9
    @21
    simp2rl
    #
    @42
    @9
    @16
    @17
    @19
    @20
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
    cV
    cW
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4.f
    cdleme4.g
    cdleme7.v
    cdleme7b
    syl113anc
    #
    cA
    @27
    c.or
    cK
    cF
    cV
    @33
    cdleme4.j
    cdleme4.a
    hlatjcl
    syl3anc
    @27
    cK
    c.le
    c.an
    @18
    @23
    @33
    cdleme4.l
    cdleme4.m
    latmle2
    syl3anc
    syl5eqbr
    @22
    @24
    cF
    cW
    c.le
    wbr
    #
    @22
    @2
    @5
    @8
    @15
    @17
    @20
    @46
    wn
    @37
    @38
    @39
    @40
    @41
    @42
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
    @22
    @24
    cF
    cU
    cV
    c.or
    co
    #
    c.le
    wbr
    #
    @46
    @22
    @0
    cU
    cA
    wcel
    #
    @35
    @36
    cU
    cV
    wne
    #
    @24
    @48
    wi
    @30
    @22
    @2
    @5
    @6
    @17
    @49
    @37
    @38
    @32
    @41
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
    #
    @43
    @45
    @22
    @2
    @5
    @6
    @16
    @21
    @50
    @37
    @38
    @32
    @9
    @16
    @21
    simp2
    @9
    @16
    @21
    simp3
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
    cV
    cW
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4.f
    cdleme4.g
    cdleme7.v
    cdleme7c
    syl311anc
    cA
    cU
    cF
    cV
    c.or
    cK
    c.le
    cdleme4.l
    cdleme4.j
    cdleme4.a
    hlatexch2
    syl131anc
    @22
    @48
    @47
    cW
    c.le
    wbr
    #
    @46
    @22
    cU
    cW
    c.le
    wbr
    #
    cV
    cW
    c.le
    wbr
    #
    @52
    @22
    cU
    @18
    cW
    c.an
    co
    #
    cW
    c.le
    cdleme4.u
    @22
    @26
    @28
    cW
    @27
    wcel
    #
    @55
    cW
    c.le
    wbr
    @31
    @34
    @22
    @1
    @56
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
    @33
    cdleme4.h
    lhpbase
    syl
    #
    @27
    cK
    c.le
    c.an
    @18
    cW
    @33
    cdleme4.l
    cdleme4.m
    latmle2
    syl3anc
    syl5eqbr
    @22
    cV
    cR
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    cW
    c.le
    cdleme7.v
    @22
    @26
    @58
    @27
    wcel
    #
    @56
    @59
    cW
    c.le
    wbr
    @31
    @22
    @0
    @10
    @13
    @60
    @30
    @10
    @11
    @15
    @9
    @21
    simp2ll
    @44
    cA
    @27
    c.or
    cK
    cR
    cS
    @33
    cdleme4.j
    cdleme4.a
    hlatjcl
    syl3anc
    @57
    @27
    cK
    c.le
    c.an
    @58
    cW
    @33
    cdleme4.l
    cdleme4.m
    latmle2
    syl3anc
    syl5eqbr
    @22
    @26
    cU
    @27
    wcel
    #
    cV
    @27
    wcel
    #
    @56
    @53
    @54
    wa
    @52
    wb
    @31
    @22
    @49
    @61
    @51
    cA
    @27
    cU
    cK
    @33
    cdleme4.a
    atbase
    syl
    @22
    @36
    @62
    @45
    cA
    @27
    cV
    cK
    @33
    cdleme4.a
    atbase
    syl
    @57
    @27
    c.or
    cK
    c.le
    cU
    cV
    cW
    @33
    cdleme4.l
    cdleme4.j
    latjle12
    syl13anc
    mpbi2and
    @22
    @26
    cF
    @27
    wcel
    #
    @47
    @27
    wcel
    #
    @56
    @48
    @52
    wa
    @46
    wi
    @31
    @22
    @35
    @63
    @43
    cA
    @27
    cF
    cK
    @33
    cdleme4.a
    atbase
    syl
    @22
    @0
    @49
    @36
    @64
    @30
    @51
    @45
    cA
    @27
    c.or
    cK
    cU
    cV
    @33
    cdleme4.j
    cdleme4.a
    hlatjcl
    syl3anc
    @57
    @27
    cK
    c.le
    cF
    @47
    cW
    @33
    cdleme4.l
    lattr
    syl13anc
    mpan2d
    syld
    mtod
    cG
    cU
    @23
    c.le
    nbrne2
    syl2anc
end
