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
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21l.mm"
include "simp231.mm"
include "simp232.mm"
include "simp3ll.mm"
include "simp3r.mm"
include "cdleme21c.mm"
include "syl332anc.mm"
include "simp233.mm"
include "clc.mm"
include "wi.mm"
include "simp11l.mm"
include "hlcvl.mm"
include "syl.mm"
include "simp11r.mm"
include "simp12l.mm"
include "simp12r.mm"
include "cdleme0a.mm"
include "syl222anc.mm"
include "simp22l.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "simp21r.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "simp22r.mm"
include "cvlatexch3.mm"
include "syl132anc.mm"
include "mpd.mm"
include "adantr.mm"
include "simp3lr.mm"
include "imp.mm"
include "eqtrd.mm"
include "ex.mm"
include "hlatlej2.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "cdleme21a.mm"
include "syl322anc.mm"
include "cvlatexch2.mm"
include "syl131anc.mm"
include "3syld.mm"
include "mtod.mm"

theorem cdleme21ct
  let vz: setvar z
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ Q e. A ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) /\ U .<_ ( S .\/ T ) ) ) /\ ( ( z e. A /\ -. z .<_ W ) /\ ( P .\/ z ) = ( S .\/ z ) ) ) -> -. U .<_ ( T .\/ z ) )

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
    cP
    cQ
    c.or
    co
    #
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
    vz
    cv
    #
    cA
    wcel
    #
    @20
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cP
    @20
    c.or
    co
    cS
    @20
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
    cT
    @20
    c.or
    co
    c.le
    wbr
    #
    cU
    @24
    c.le
    wbr
    #
    @27
    @2
    @5
    @6
    @8
    @14
    @16
    @21
    @25
    @29
    wn
    @2
    @5
    @6
    @19
    @26
    simp11
    @2
    @5
    @6
    @19
    @26
    simp12
    @2
    @5
    @6
    @19
    @26
    simp13
    #
    @8
    @9
    @13
    @18
    @7
    @26
    simp21l
    #
    @14
    @16
    @17
    @10
    @13
    @7
    @26
    simp231
    #
    @14
    @16
    @17
    @10
    @13
    @7
    @26
    simp232
    #
    @21
    @22
    @25
    @7
    @19
    simp3ll
    #
    @7
    @19
    @23
    @25
    simp3r
    #
    vz
    cA
    cP
    cQ
    cS
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
    cdleme21c
    syl332anc
    @27
    @28
    cU
    cS
    c.or
    co
    #
    cU
    @20
    c.or
    co
    #
    wceq
    #
    cS
    @37
    c.le
    wbr
    #
    @29
    @27
    @28
    @38
    @27
    @28
    wa
    @36
    cU
    cT
    c.or
    co
    #
    @37
    @27
    @36
    @40
    wceq
    #
    @28
    @27
    @17
    @41
    @14
    @16
    @17
    @10
    @13
    @7
    @26
    simp233
    @27
    cK
    clc
    wcel
    #
    cU
    cA
    wcel
    #
    @8
    @11
    cU
    cS
    wne
    #
    cU
    cT
    wne
    #
    @17
    @41
    wi
    @27
    @0
    @42
    @0
    @1
    @5
    @6
    @19
    @26
    simp11l
    #
    cK
    hlcvl
    syl
    #
    @27
    @0
    @1
    @3
    @4
    @6
    @14
    @43
    @46
    @0
    @1
    @5
    @6
    @19
    @26
    simp11r
    #
    @3
    @4
    @2
    @6
    @19
    @26
    simp12l
    #
    @3
    @4
    @2
    @6
    @19
    @26
    simp12r
    @30
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
    cdleme0a
    syl222anc
    #
    @31
    @11
    @12
    @10
    @18
    @7
    @26
    simp22l
    #
    @27
    cU
    cW
    c.le
    wbr
    #
    @9
    @44
    @27
    cU
    @15
    cW
    c.an
    co
    #
    cW
    c.le
    cdleme21.u
    @27
    cK
    clat
    wcel
    #
    @15
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @55
    wcel
    #
    @53
    cW
    c.le
    wbr
    @27
    @0
    @54
    @46
    cK
    hllat
    syl
    @27
    @0
    @3
    @6
    @56
    @46
    @49
    @30
    cA
    @55
    c.or
    cK
    cP
    cQ
    @55
    eqid
    #
    cdleme21.j
    cdleme21.a
    hlatjcl
    syl3anc
    @27
    @1
    @57
    @48
    @55
    cH
    cK
    cW
    @58
    cdleme21.h
    lhpbase
    syl
    @55
    cK
    c.le
    c.an
    @15
    cW
    @58
    cdleme21.l
    cdleme21.m
    latmle2
    syl3anc
    syl5eqbr
    #
    @8
    @9
    @13
    @18
    @7
    @26
    simp21r
    cU
    cS
    cW
    c.le
    nbrne2
    syl2anc
    @27
    @52
    @12
    @45
    @59
    @11
    @12
    @10
    @18
    @7
    @26
    simp22r
    cU
    cT
    cW
    c.le
    nbrne2
    syl2anc
    #
    cA
    cU
    cS
    cT
    c.or
    cK
    c.le
    cdleme21.l
    cdleme21.j
    cdleme21.a
    cvlatexch3
    syl132anc
    mpd
    adantr
    @27
    @28
    @40
    @37
    wceq
    #
    @27
    @42
    @43
    @11
    @21
    @45
    cU
    @20
    wne
    #
    @28
    @61
    wi
    @47
    @50
    @51
    @34
    @60
    @27
    @52
    @22
    @62
    @59
    @21
    @22
    @25
    @7
    @19
    simp3lr
    cU
    @20
    cW
    c.le
    nbrne2
    syl2anc
    cA
    cU
    cT
    @20
    c.or
    cK
    c.le
    cdleme21.l
    cdleme21.j
    cdleme21.a
    cvlatexch3
    syl132anc
    imp
    eqtrd
    ex
    @27
    cS
    @36
    c.le
    wbr
    #
    @38
    @39
    @27
    @0
    @43
    @8
    @63
    @46
    @50
    @31
    cA
    cU
    cS
    c.or
    cK
    c.le
    cdleme21.l
    cdleme21.j
    cdleme21.a
    hlatlej2
    syl3anc
    @36
    @37
    cS
    c.le
    breq2
    syl5ibcom
    @27
    @42
    @8
    @43
    @21
    cS
    @20
    wne
    #
    @39
    @29
    wi
    @47
    @31
    @50
    @34
    @27
    @0
    @3
    @6
    @8
    @16
    @21
    @25
    @64
    @46
    @49
    @30
    @31
    @33
    @34
    @35
    vz
    cA
    cP
    cQ
    cS
    c.or
    cK
    c.le
    cdleme21.l
    cdleme21.j
    cdleme21.a
    cdleme21a
    syl322anc
    cA
    cS
    cU
    @20
    c.or
    cK
    c.le
    cdleme21.l
    cdleme21.j
    cdleme21.a
    cvlatexch2
    syl131anc
    3syld
    mtod
end
