include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "simp23.mm"
include "clc.mm"
include "simp11l.mm"
include "hlcvl.mm"
include "syl.mm"
include "simp12l.mm"
include "simp21.mm"
include "simp3l.mm"
include "simp13.mm"
include "atnlej1.mm"
include "necomd.mm"
include "syl131anc.mm"
include "simp3r.mm"
include "cvlsupr7.mm"
include "syl132anc.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "wi.mm"
include "simp11r.mm"
include "simp12r.mm"
include "simp22.mm"
include "cdleme0a.mm"
include "syl222anc.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "cvlatexch1.mm"
include "hlatlej1.mm"
include "cdlemeulpq.mm"
include "syl22anc.mm"
include "wb.mm"
include "atbase.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "lattr.mm"
include "mpan2d.mm"
include "syld.mm"
include "sylbird.mm"
include "mtod.mm"

theorem cdleme21c
  let vz: setvar z
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme21.l: |- .<_ = ( le ` K )
  assume cdleme21.j: |- .\/ = ( join ` K )
  assume cdleme21.m: |- ./\ = ( meet ` K )
  assume cdleme21.a: |- A = ( Atoms ` K )
  assume cdleme21.h: |- H = ( LHyp ` K )
  assume cdleme21.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ Q e. A ) /\ ( S e. A /\ P =/= Q /\ -. S .<_ ( P .\/ Q ) ) /\ ( z e. A /\ ( P .\/ z ) = ( S .\/ z ) ) ) -> -. U .<_ ( S .\/ z ) )

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
    w3a
    #
    cS
    cA
    wcel
    #
    cP
    cQ
    wne
    #
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    vz
    cv
    #
    cA
    wcel
    #
    cP
    @14
    c.or
    co
    cS
    @14
    c.or
    co
    #
    wceq
    #
    wa
    #
    w3a
    #
    cU
    @16
    c.le
    wbr
    #
    @11
    @7
    @8
    @9
    @12
    @18
    simp23
    #
    @19
    @20
    cU
    cP
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    @11
    @19
    @22
    @16
    cU
    c.le
    @19
    @22
    @14
    cS
    c.or
    co
    #
    @16
    @19
    cK
    clc
    wcel
    #
    @3
    @8
    @15
    cP
    cS
    wne
    #
    @17
    @22
    @24
    wceq
    @19
    @0
    @25
    @0
    @1
    @5
    @6
    @13
    @18
    simp11l
    #
    cK
    hlcvl
    syl
    #
    @3
    @4
    @2
    @6
    @13
    @18
    simp12l
    #
    @7
    @8
    @9
    @12
    @18
    simp21
    #
    @7
    @13
    @15
    @17
    simp3l
    #
    @19
    @0
    @8
    @3
    @6
    @12
    @26
    @27
    @30
    @29
    @2
    @5
    @6
    @13
    @18
    simp13
    #
    @21
    @0
    @8
    @3
    @6
    w3a
    @12
    w3a
    cS
    cP
    cA
    cS
    cP
    cQ
    c.or
    cK
    c.le
    cdleme21.l
    cdleme21.j
    cdleme21.a
    atnlej1
    necomd
    syl131anc
    @7
    @13
    @15
    @17
    simp3r
    cA
    cP
    cS
    @14
    c.or
    cK
    cdleme21.a
    cdleme21.j
    cvlsupr7
    syl132anc
    @19
    @0
    @15
    @8
    @24
    @16
    wceq
    @27
    @31
    @30
    cA
    c.or
    cK
    @14
    cS
    cdleme21.j
    cdleme21.a
    hlatjcom
    syl3anc
    eqtrd
    breq2d
    @19
    @23
    cS
    cP
    cU
    c.or
    co
    #
    c.le
    wbr
    #
    @11
    @19
    @25
    cU
    cA
    wcel
    #
    @8
    @3
    cU
    cP
    wne
    #
    @23
    @34
    wi
    @28
    @19
    @0
    @1
    @3
    @4
    @6
    @9
    @35
    @27
    @0
    @1
    @5
    @6
    @13
    @18
    simp11r
    #
    @29
    @3
    @4
    @2
    @6
    @13
    @18
    simp12r
    #
    @32
    @7
    @8
    @9
    @12
    @18
    simp22
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
    cdleme21.l
    cdleme21.j
    cdleme21.m
    cdleme21.a
    cdleme21.h
    cdleme21.u
    cdleme0a
    syl222anc
    #
    @30
    @29
    @19
    cU
    cW
    c.le
    wbr
    @4
    @36
    @19
    cU
    @10
    cW
    c.an
    co
    #
    cW
    c.le
    cdleme21.u
    @19
    cK
    clat
    wcel
    #
    @10
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @42
    wcel
    #
    @40
    cW
    c.le
    wbr
    @19
    @0
    @41
    @27
    cK
    hllat
    syl
    #
    @19
    @0
    @3
    @6
    @43
    @27
    @29
    @32
    cA
    @42
    c.or
    cK
    cP
    cQ
    @42
    eqid
    #
    cdleme21.j
    cdleme21.a
    hlatjcl
    syl3anc
    #
    @19
    @1
    @44
    @37
    @42
    cH
    cK
    cW
    @46
    cdleme21.h
    lhpbase
    syl
    @42
    cK
    c.le
    c.an
    @10
    cW
    @46
    cdleme21.l
    cdleme21.m
    latmle2
    syl3anc
    syl5eqbr
    @38
    cU
    cP
    cW
    c.le
    nbrne2
    syl2anc
    cA
    cU
    cS
    cP
    c.or
    cK
    c.le
    cdleme21.l
    cdleme21.j
    cdleme21.a
    cvlatexch1
    syl131anc
    @19
    @34
    @33
    @10
    c.le
    wbr
    #
    @11
    @19
    cP
    @10
    c.le
    wbr
    #
    cU
    @10
    c.le
    wbr
    #
    @48
    @19
    @0
    @3
    @6
    @49
    @27
    @29
    @32
    cA
    cP
    cQ
    c.or
    cK
    c.le
    cdleme21.l
    cdleme21.j
    cdleme21.a
    hlatlej1
    syl3anc
    @19
    @0
    @1
    @3
    @6
    @50
    @27
    @37
    @29
    @32
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
    cdleme21.l
    cdleme21.j
    cdleme21.m
    cdleme21.a
    cdleme21.h
    cdleme21.u
    cdlemeulpq
    syl22anc
    @19
    @41
    cP
    @42
    wcel
    #
    cU
    @42
    wcel
    #
    @43
    @49
    @50
    wa
    @48
    wb
    @45
    @19
    @3
    @51
    @29
    cA
    @42
    cP
    cK
    @46
    cdleme21.a
    atbase
    syl
    @19
    @35
    @52
    @39
    cA
    @42
    cU
    cK
    @46
    cdleme21.a
    atbase
    syl
    @47
    @42
    c.or
    cK
    c.le
    cP
    cU
    @10
    @46
    cdleme21.l
    cdleme21.j
    latjle12
    syl13anc
    mpbi2and
    @19
    @41
    cS
    @42
    wcel
    #
    @33
    @42
    wcel
    #
    @43
    @34
    @48
    wa
    @11
    wi
    @45
    @19
    @8
    @53
    @30
    cA
    @42
    cS
    cK
    @46
    cdleme21.a
    atbase
    syl
    @19
    @0
    @3
    @35
    @54
    @27
    @29
    @39
    cA
    @42
    c.or
    cK
    cP
    cU
    @46
    cdleme21.j
    cdleme21.a
    hlatjcl
    syl3anc
    @47
    @42
    cK
    c.le
    cS
    @33
    @10
    @46
    cdleme21.l
    lattr
    syl13anc
    mpan2d
    syld
    sylbird
    mtod
end
