include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
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
include "simp11r.mm"
include "simp22.mm"
include "cdleme1b.mm"
include "syl23anc.mm"
include "simp21l.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latjcl.mm"
include "latmle2.mm"
include "wceq.mm"
include "simp21.mm"
include "simp3l.mm"
include "simp23l.mm"
include "simp23r.mm"
include "simp3r.mm"
include "hlatjcom.mm"
include "breqtrd.mm"
include "clc.mm"
include "wi.mm"
include "hlcvl.mm"
include "cvlatexch2.mm"
include "syl131anc.mm"
include "mpd.mm"
include "cdleme22aa.mm"
include "syl233anc.mm"
include "oveq2d.mm"
include "breqtrrd.mm"
include "syl5eqbr.mm"

theorem cdleme22f
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cV: class V
  let cW: class W
  assume cdleme22.l: |- .<_ = ( le ` K )
  assume cdleme22.j: |- .\/ = ( join ` K )
  assume cdleme22.m: |- ./\ = ( meet ` K )
  assume cdleme22.a: |- A = ( Atoms ` K )
  assume cdleme22.h: |- H = ( LHyp ` K )
  assume cdleme22f.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme22f.f: |- F = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme22f.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ ( ( S .\/ T ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ T e. A /\ ( V e. A /\ V .<_ W ) ) /\ ( S =/= T /\ S .<_ ( T .\/ V ) ) ) -> N .<_ ( F .\/ V ) )

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
    cV
    cA
    wcel
    #
    cV
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cS
    cT
    wne
    #
    cS
    cT
    cV
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cN
    cP
    cQ
    c.or
    co
    #
    cF
    cS
    cT
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
    cF
    cV
    c.or
    co
    #
    c.le
    cdleme22f.n
    @22
    @27
    @26
    @28
    c.le
    @22
    cK
    clat
    wcel
    #
    @23
    cK
    cbs
    cfv
    #
    wcel
    #
    @26
    @30
    wcel
    #
    @27
    @26
    c.le
    wbr
    @22
    @0
    @29
    @0
    @1
    @5
    @8
    @17
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
    @31
    @33
    @3
    @4
    @2
    @8
    @17
    @21
    simp12l
    #
    @6
    @7
    @2
    @5
    @17
    @21
    simp13l
    #
    cA
    @30
    c.or
    cK
    cP
    cQ
    @30
    eqid
    #
    cdleme22.j
    cdleme22.a
    hlatjcl
    syl3anc
    @22
    @29
    cF
    @30
    wcel
    #
    @25
    @30
    wcel
    #
    @32
    @34
    @22
    @0
    @1
    @3
    @6
    @13
    @38
    @33
    @0
    @1
    @5
    @8
    @17
    @21
    simp11r
    #
    @35
    @36
    @9
    @12
    @13
    @16
    @21
    simp22
    #
    cA
    @30
    cP
    cQ
    cT
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    cdleme22.h
    cdleme22f.u
    cdleme22f.f
    @37
    cdleme1b
    syl23anc
    @22
    @29
    @24
    @30
    wcel
    #
    cW
    @30
    wcel
    #
    @39
    @34
    @22
    @0
    @10
    @13
    @42
    @33
    @10
    @11
    @13
    @16
    @9
    @21
    simp21l
    #
    @41
    cA
    @30
    c.or
    cK
    cS
    cT
    @37
    cdleme22.j
    cdleme22.a
    hlatjcl
    syl3anc
    @22
    @1
    @43
    @40
    @30
    cH
    cK
    cW
    @37
    cdleme22.h
    lhpbase
    syl
    @30
    cK
    c.an
    @24
    cW
    @37
    cdleme22.m
    latmcl
    syl3anc
    @30
    c.or
    cK
    cF
    @25
    @37
    cdleme22.j
    latjcl
    syl3anc
    @30
    cK
    c.le
    c.an
    @23
    @26
    @37
    cdleme22.l
    cdleme22.m
    latmle2
    syl3anc
    @22
    cV
    @25
    cF
    c.or
    @22
    @0
    @1
    @12
    @13
    @18
    @14
    @15
    cV
    @24
    c.le
    wbr
    #
    cV
    @25
    wceq
    @33
    @40
    @9
    @12
    @13
    @16
    @21
    simp21
    @41
    @9
    @17
    @18
    @20
    simp3l
    #
    @14
    @15
    @12
    @13
    @9
    @21
    simp23l
    #
    @14
    @15
    @12
    @13
    @9
    @21
    simp23r
    @22
    cS
    cV
    cT
    c.or
    co
    #
    c.le
    wbr
    #
    @45
    @22
    cS
    @19
    @48
    c.le
    @9
    @17
    @18
    @20
    simp3r
    @22
    @0
    @13
    @14
    @19
    @48
    wceq
    @33
    @41
    @47
    cA
    c.or
    cK
    cT
    cV
    cdleme22.j
    cdleme22.a
    hlatjcom
    syl3anc
    breqtrd
    @22
    cK
    clc
    wcel
    #
    @10
    @14
    @13
    @18
    @49
    @45
    wi
    @22
    @0
    @50
    @33
    cK
    hlcvl
    syl
    @44
    @47
    @41
    @46
    cA
    cS
    cV
    cT
    c.or
    cK
    c.le
    cdleme22.l
    cdleme22.j
    cdleme22.a
    cvlatexch2
    syl131anc
    mpd
    cA
    cS
    cT
    @25
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    cdleme22.h
    @25
    eqid
    cdleme22aa
    syl233anc
    oveq2d
    breqtrrd
    syl5eqbr
end
