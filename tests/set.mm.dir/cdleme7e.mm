include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cp0.mm"
include "cfv.mm"
include "cbs.mm"
include "ccvr.mm"
include "simp11l.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp2ll.mm"
include "eqid.mm"
include "atbase.mm"
include "cops.mm"
include "hlop.mm"
include "op0cl.mm"
include "3syl.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp12l.mm"
include "simp13l.mm"
include "hlatjcl.mm"
include "simp11.mm"
include "simp2rl.mm"
include "cdleme1b.mm"
include "syl13anc.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl5eqel.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "simp2lr.mm"
include "nbrne2.mm"
include "necomd.mm"
include "syl2anc.mm"
include "wb.mm"
include "simp12.mm"
include "simp31.mm"
include "lhpat2.mm"
include "syl112anc.mm"
include "atcvr1.mm"
include "mpbid.mm"
include "col.mm"
include "wceq.mm"
include "hlol.mm"
include "olj01.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp32.mm"
include "cdleme5.mm"
include "syl132anc.mm"
include "cdleme4.mm"
include "syl131anc.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "cvrne.mm"
include "syl31anc.mm"
include "oveq2.mm"
include "necon3i.mm"

theorem cdleme7e
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( P =/= Q /\ R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> G =/= ( 0. ` K ) )

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
    cK
    cp0
    cfv
    #
    cG
    @22
    cR
    @23
    c.or
    co
    #
    cR
    cG
    c.or
    co
    #
    wne
    #
    @23
    cG
    wne
    @22
    @0
    @24
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
    @24
    @25
    cK
    ccvr
    cfv
    #
    wbr
    @26
    @0
    @1
    @5
    @8
    @16
    @21
    simp11l
    #
    @22
    cK
    clat
    wcel
    #
    cR
    @27
    wcel
    #
    @23
    @27
    wcel
    #
    @28
    @22
    @0
    @32
    @31
    cK
    hllat
    syl
    #
    @22
    @10
    @33
    @10
    @11
    @15
    @9
    @21
    simp2ll
    #
    cA
    @27
    cR
    cK
    @27
    eqid
    #
    cdleme4.a
    atbase
    syl
    #
    @22
    @0
    cK
    cops
    wcel
    @34
    @31
    cK
    hlop
    @27
    cK
    @23
    @37
    @23
    eqid
    #
    op0cl
    3syl
    @27
    c.or
    cK
    cR
    @23
    @37
    cdleme4.j
    latjcl
    syl3anc
    @22
    @32
    @33
    cG
    @27
    wcel
    @29
    @35
    @38
    @22
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
    @27
    cdleme4.g
    @22
    @32
    @18
    @27
    wcel
    #
    @42
    @27
    wcel
    #
    @43
    @27
    wcel
    @35
    @22
    @0
    @3
    @6
    @44
    @31
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
    @37
    cdleme4.j
    cdleme4.a
    hlatjcl
    syl3anc
    #
    @22
    @32
    cF
    @27
    wcel
    #
    @41
    @27
    wcel
    #
    @45
    @35
    @22
    @2
    @3
    @6
    @13
    @49
    @2
    @5
    @8
    @16
    @21
    simp11
    #
    @46
    @47
    @13
    @14
    @12
    @9
    @21
    simp2rl
    #
    cA
    @27
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
    @37
    cdleme1b
    syl13anc
    @22
    @32
    @40
    @27
    wcel
    #
    cW
    @27
    wcel
    #
    @50
    @35
    @22
    @0
    @10
    @13
    @53
    @31
    @36
    @52
    cA
    @27
    c.or
    cK
    cR
    cS
    @37
    cdleme4.j
    cdleme4.a
    hlatjcl
    syl3anc
    @22
    @1
    @54
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
    @37
    cdleme4.h
    lhpbase
    syl
    #
    @27
    cK
    c.an
    @40
    cW
    @37
    cdleme4.m
    latmcl
    syl3anc
    @27
    c.or
    cK
    cF
    @41
    @37
    cdleme4.j
    latjcl
    syl3anc
    @27
    cK
    c.an
    @18
    @42
    @37
    cdleme4.m
    latmcl
    syl3anc
    syl5eqel
    @27
    c.or
    cK
    cR
    cG
    @37
    cdleme4.j
    latjcl
    syl3anc
    @22
    cR
    cR
    cU
    c.or
    co
    #
    @24
    @25
    @30
    @22
    cR
    cU
    wne
    #
    cR
    @56
    @30
    wbr
    #
    @22
    cU
    cW
    c.le
    wbr
    #
    @11
    @57
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
    @32
    @44
    @54
    @60
    cW
    c.le
    wbr
    @35
    @48
    @55
    @27
    cK
    c.le
    c.an
    @18
    cW
    @37
    cdleme4.l
    cdleme4.m
    latmle2
    syl3anc
    syl5eqbr
    @10
    @11
    @15
    @9
    @21
    simp2lr
    @59
    @11
    wa
    cU
    cR
    cU
    cR
    cW
    c.le
    nbrne2
    necomd
    syl2anc
    @22
    @0
    @10
    cU
    cA
    wcel
    #
    @57
    @58
    wb
    @31
    @36
    @22
    @2
    @5
    @6
    @17
    @61
    @51
    @2
    @5
    @8
    @16
    @21
    simp12
    @47
    @9
    @16
    @17
    @19
    @20
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
    @30
    cR
    cU
    c.or
    cK
    cdleme4.j
    @30
    eqid
    #
    cdleme4.a
    atcvr1
    syl3anc
    mpbid
    @22
    cK
    col
    wcel
    #
    @33
    @24
    cR
    wceq
    @22
    @0
    @63
    @31
    cK
    hlol
    syl
    @38
    @27
    c.or
    cK
    cR
    @23
    @37
    cdleme4.j
    @39
    olj01
    syl2anc
    @22
    @25
    @18
    @56
    @22
    @2
    @3
    @6
    @12
    @15
    @19
    @25
    @18
    wceq
    @51
    @46
    @47
    @9
    @12
    @15
    @21
    simp2l
    #
    @9
    @12
    @15
    @21
    simp2r
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
    cW
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4.f
    cdleme4.g
    cdleme5
    syl132anc
    @22
    @2
    @3
    @6
    @12
    @19
    @18
    @56
    wceq
    @51
    @46
    @47
    @64
    @65
    cA
    cP
    cQ
    cR
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
    cdleme4
    syl131anc
    eqtrd
    3brtr4d
    chlt
    @27
    @30
    cK
    @24
    @25
    @37
    @62
    cvrne
    syl31anc
    @23
    cG
    @24
    @25
    @23
    cG
    cR
    c.or
    oveq2
    necon3i
    syl
    necomd
end
