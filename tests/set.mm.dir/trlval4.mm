include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "simp3r.mm"
include "simpl1l.mm"
include "simp23l.mm"
include "adantr.mm"
include "simpl1.mm"
include "simpl21.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "hlatlej1.mm"
include "simpl22.mm"
include "trljat1.mm"
include "simpr.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "wi.mm"
include "simpl3r.mm"
include "cp0.mm"
include "simpll1.mm"
include "eqid.mm"
include "trl0.mm"
include "syl112anc.mm"
include "cal.mm"
include "cbs.mm"
include "hlatl.mm"
include "syl.mm"
include "simp22l.mm"
include "hlatjcl.mm"
include "atl0le.mm"
include "syl2anc.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "necon3bd.mm"
include "mpd.mm"
include "trlat.mm"
include "simpl3l.mm"
include "necomd.mm"
include "hlatexch1.mm"
include "syl131anc.mm"
include "trlval3.mm"
include "syl113anc.mm"

theorem trlval4
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume trlval3.l: |- .<_ = ( le ` K )
  assume trlval3.j: |- .\/ = ( join ` K )
  assume trlval3.m: |- ./\ = ( meet ` K )
  assume trlval3.a: |- A = ( Atoms ` K )
  assume trlval3.h: |- H = ( LHyp ` K )
  assume trlval3.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlval3.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ -. ( R ` F ) .<_ ( P .\/ Q ) ) ) -> ( R ` F ) = ( ( P .\/ ( F ` P ) ) ./\ ( Q .\/ ( F ` Q ) ) ) )

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
    cF
    cT
    wcel
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
    cP
    cQ
    wne
    #
    cF
    cR
    cfv
    #
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
    wa
    #
    w3a
    #
    @2
    @3
    @6
    @9
    cP
    cP
    cF
    cfv
    #
    c.or
    co
    #
    cQ
    cQ
    cF
    cfv
    #
    c.or
    co
    #
    wne
    #
    @12
    @19
    @21
    c.an
    co
    wceq
    @2
    @10
    @16
    simp1
    @2
    @3
    @6
    @9
    @16
    simp21
    @2
    @3
    @6
    @9
    @16
    simp22
    @2
    @3
    @6
    @9
    @16
    simp23
    @17
    @15
    @22
    @2
    @10
    @11
    @15
    simp3r
    @17
    @14
    @19
    @21
    @17
    @19
    @21
    wceq
    #
    @14
    @17
    @23
    wa
    #
    cQ
    cP
    @12
    c.or
    co
    #
    c.le
    wbr
    #
    @14
    @24
    cQ
    @21
    @25
    c.le
    @24
    @0
    @7
    @20
    cA
    wcel
    #
    cQ
    @21
    c.le
    wbr
    @0
    @1
    @10
    @16
    @23
    simpl1l
    #
    @17
    @7
    @23
    @7
    @8
    @3
    @6
    @2
    @16
    simp23l
    adantr
    #
    @24
    @2
    @3
    @7
    @27
    @2
    @10
    @16
    @23
    simpl1
    #
    @3
    @6
    @9
    @2
    @16
    @23
    simpl21
    #
    @29
    cA
    cQ
    cT
    cF
    cH
    cK
    c.le
    cW
    trlval3.l
    trlval3.a
    trlval3.h
    trlval3.t
    ltrnat
    syl3anc
    cA
    cQ
    @20
    c.or
    cK
    c.le
    trlval3.l
    trlval3.j
    trlval3.a
    hlatlej1
    syl3anc
    @24
    @25
    @19
    @21
    @24
    @2
    @3
    @6
    @25
    @19
    wceq
    @30
    @31
    @3
    @6
    @9
    @2
    @16
    @23
    simpl22
    #
    cA
    cP
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    cW
    trlval3.l
    trlval3.j
    trlval3.a
    trlval3.h
    trlval3.t
    trlval3.r
    trljat1
    syl3anc
    @17
    @23
    simpr
    eqtrd
    breqtrrd
    @24
    @0
    @7
    @12
    cA
    wcel
    #
    @4
    cQ
    cP
    wne
    @26
    @14
    wi
    @28
    @29
    @24
    @2
    @6
    @3
    @18
    cP
    wne
    #
    @33
    @30
    @32
    @31
    @24
    @15
    @34
    @11
    @15
    @2
    @10
    @23
    simpl3r
    @24
    @14
    @18
    cP
    @24
    @18
    cP
    wceq
    #
    @14
    @24
    @35
    wa
    #
    @12
    cK
    cp0
    cfv
    #
    @13
    c.le
    @36
    @2
    @6
    @3
    @35
    @12
    @37
    wceq
    @2
    @10
    @16
    @23
    @35
    simpll1
    @24
    @6
    @35
    @32
    adantr
    @24
    @3
    @35
    @31
    adantr
    @24
    @35
    simpr
    cA
    cP
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    @37
    trlval3.l
    @37
    eqid
    #
    trlval3.a
    trlval3.h
    trlval3.t
    trlval3.r
    trl0
    syl112anc
    @24
    @37
    @13
    c.le
    wbr
    #
    @35
    @24
    cK
    cal
    wcel
    #
    @13
    cK
    cbs
    cfv
    #
    wcel
    #
    @39
    @24
    @0
    @40
    @28
    cK
    hlatl
    syl
    @24
    @0
    @4
    @7
    @42
    @28
    @17
    @4
    @23
    @4
    @5
    @3
    @9
    @2
    @16
    simp22l
    adantr
    #
    @29
    cA
    @41
    c.or
    cK
    cP
    cQ
    @41
    eqid
    #
    trlval3.j
    trlval3.a
    hlatjcl
    syl3anc
    @41
    cK
    c.le
    @13
    @37
    @44
    trlval3.l
    @38
    atl0le
    syl2anc
    adantr
    eqbrtrd
    ex
    necon3bd
    mpd
    cA
    cP
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    trlval3.l
    trlval3.a
    trlval3.h
    trlval3.t
    trlval3.r
    trlat
    syl112anc
    @43
    @24
    cP
    cQ
    @11
    @15
    @2
    @10
    @23
    simpl3l
    necomd
    cA
    cQ
    @12
    cP
    c.or
    cK
    c.le
    trlval3.l
    trlval3.j
    trlval3.a
    hlatexch1
    syl131anc
    mpd
    ex
    necon3bd
    mpd
    cA
    cP
    cQ
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    trlval3.l
    trlval3.j
    trlval3.m
    trlval3.a
    trlval3.h
    trlval3.t
    trlval3.r
    trlval3
    syl113anc
end
