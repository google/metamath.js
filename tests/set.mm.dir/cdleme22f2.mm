include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wne.mm"
include "w3a.mm"
include "simp11.mm"
include "simp2l.mm"
include "simp2r.mm"
include "3jca.mm"
include "simp12.mm"
include "simp31l.mm"
include "simp33.mm"
include "simp32l.mm"
include "necomd.mm"
include "simp32r.mm"
include "clc.mm"
include "wi.mm"
include "simp11l.mm"
include "hlcvl.mm"
include "syl.mm"
include "simp12l.mm"
include "simp33l.mm"
include "simp33r.mm"
include "simp31r.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "cvlatexch2.mm"
include "syl131anc.mm"
include "mpd.mm"
include "cdleme22f.mm"
include "syl132anc.mm"
include "simp31.mm"
include "simp133.mm"
include "simp132.mm"
include "simp131.mm"
include "cdleme7ga.mm"
include "syl123anc.mm"
include "cdleme3fa.mm"
include "cdleme7.mm"

theorem cdleme22f2
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
  assume cdleme22f2.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme22f2.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme22f2.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ ( ( T .\/ S ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( T e. A /\ -. T .<_ W ) /\ ( -. S .<_ ( P .\/ Q ) /\ T .<_ ( P .\/ Q ) /\ P =/= Q ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( S =/= T /\ S .<_ ( T .\/ V ) ) /\ ( V e. A /\ V .<_ W ) ) ) -> F .<_ ( N .\/ V ) )

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
    @6
    c.le
    wbr
    #
    cP
    cQ
    wne
    #
    w3a
    #
    w3a
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
    cS
    cT
    wne
    #
    cS
    cT
    cV
    c.or
    co
    c.le
    wbr
    #
    wa
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
    w3a
    #
    cN
    cF
    cV
    c.or
    co
    c.le
    wbr
    #
    cF
    cN
    cV
    c.or
    co
    c.le
    wbr
    #
    @25
    @2
    @12
    @13
    w3a
    #
    @5
    @15
    @23
    cT
    cS
    wne
    cT
    cS
    cV
    c.or
    co
    c.le
    wbr
    #
    @26
    @25
    @2
    @12
    @13
    @2
    @5
    @10
    @14
    @24
    simp11
    #
    @11
    @12
    @13
    @24
    simp2l
    #
    @11
    @12
    @13
    @24
    simp2r
    #
    3jca
    #
    @2
    @5
    @10
    @14
    @24
    simp12
    #
    @15
    @16
    @20
    @23
    @11
    @14
    simp31l
    #
    @11
    @14
    @17
    @20
    @23
    simp33
    @25
    cS
    cT
    @18
    @19
    @17
    @23
    @11
    @14
    simp32l
    necomd
    @25
    @19
    @29
    @18
    @19
    @17
    @23
    @11
    @14
    simp32r
    @25
    cK
    clc
    wcel
    #
    @15
    @3
    @21
    cS
    cV
    wne
    #
    @19
    @29
    wi
    @25
    @0
    @36
    @0
    @1
    @5
    @10
    @14
    @24
    simp11l
    cK
    hlcvl
    syl
    #
    @35
    @3
    @4
    @2
    @10
    @14
    @24
    simp12l
    @21
    @22
    @17
    @20
    @11
    @14
    simp33l
    #
    @25
    @22
    @16
    @37
    @21
    @22
    @17
    @20
    @11
    @14
    simp33r
    #
    @15
    @16
    @20
    @23
    @11
    @14
    simp31r
    @22
    @16
    wa
    cV
    cS
    cV
    cS
    cW
    c.le
    nbrne2
    necomd
    syl2anc
    cA
    cS
    cT
    cV
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
    cP
    cQ
    cT
    cS
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cV
    cW
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    cdleme22.h
    cdleme22f2.u
    cdleme22f2.f
    cdleme22f2.n
    cdleme22f
    syl132anc
    @25
    @36
    cN
    cA
    wcel
    #
    cF
    cA
    wcel
    #
    @21
    cN
    cV
    wne
    #
    @26
    @27
    wi
    @38
    @25
    @28
    @5
    @17
    @9
    @8
    @7
    @41
    @33
    @34
    @11
    @14
    @17
    @20
    @23
    simp31
    #
    @7
    @8
    @9
    @2
    @5
    @14
    @24
    simp133
    #
    @7
    @8
    @9
    @2
    @5
    @14
    @24
    simp132
    #
    @7
    @8
    @9
    @2
    @5
    @14
    @24
    simp131
    #
    cA
    cP
    cQ
    cT
    cS
    cU
    cF
    cN
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
    cdleme22f2.u
    cdleme22f2.f
    cdleme22f2.n
    cdleme7ga
    syl123anc
    @25
    @2
    @12
    @13
    @17
    @9
    @7
    @42
    @30
    @31
    @32
    @44
    @45
    @47
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
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    cdleme22.h
    cdleme22f2.u
    cdleme22f2.f
    cdleme3fa
    syl132anc
    @39
    @25
    @22
    cN
    cW
    c.le
    wbr
    wn
    #
    @43
    @40
    @25
    @28
    @5
    @17
    @9
    @8
    @7
    @48
    @33
    @34
    @44
    @45
    @46
    @47
    cA
    cP
    cQ
    cT
    cS
    cU
    cF
    cN
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
    cdleme22f2.u
    cdleme22f2.f
    cdleme22f2.n
    cdleme7
    syl123anc
    @22
    @48
    wa
    cV
    cN
    cV
    cN
    cW
    c.le
    nbrne2
    necomd
    syl2anc
    cA
    cN
    cF
    cV
    c.or
    cK
    c.le
    cdleme22.l
    cdleme22.j
    cdleme22.a
    cvlatexch2
    syl131anc
    mpd
end
