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
include "wmo.mm"
include "wo.mm"
include "simp23r.mm"
include "neanior.mm"
include "simpl33.mm"
include "simp23l.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "simpl32.mm"
include "clc.mm"
include "wb.mm"
include "simpl1l.mm"
include "hlcvl.mm"
include "syl.mm"
include "simp21l.mm"
include "simp22l.mm"
include "simpl31.mm"
include "cvlsupr2.mm"
include "syl131anc.mm"
include "mpbir3and.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp21r.mm"
include "simp31.mm"
include "lhpat2.mm"
include "syl222anc.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl22.mm"
include "cdleme02N.mm"
include "simpld.mm"
include "syl121anc.mm"
include "wrmo.mm"
include "df-rmo.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "rmoi.mm"
include "syl3an1br.mm"
include "syl122anc.mm"
include "simprd.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "syl5bir.mm"
include "mt3d.mm"

theorem cdleme0moN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vr: setvar r
  let vu: setvar u
  assume cdleme0.l: |- .<_ = ( le ` K )
  assume cdleme0.j: |- .\/ = ( join ` K )
  assume cdleme0.m: |- ./\ = ( meet ` K )
  assume cdleme0.a: |- A = ( Atoms ` K )
  assume cdleme0.h: |- H = ( LHyp ` K )
  assume cdleme0.u: |- U = ( ( P .\/ Q ) ./\ W )

  disjoint A r
  disjoint .\/ r
  disjoint P r
  disjoint Q r
  disjoint R r
  disjoint U r
  disjoint A u
  disjoint .\/ u
  disjoint .<_ u
  disjoint P u
  disjoint Q u
  disjoint U u
  disjoint W u
  disjoint H u
  disjoint K u
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( P =/= Q /\ R .<_ ( P .\/ Q ) /\ E* r ( r e. A /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( R = P \/ R = Q ) )

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
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    #
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
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    vr
    cv
    #
    cA
    wcel
    cP
    @16
    c.or
    co
    #
    cQ
    @16
    c.or
    co
    #
    wceq
    #
    wa
    vr
    wmo
    #
    w3a
    #
    w3a
    #
    cR
    cP
    wceq
    cR
    cQ
    wceq
    wo
    #
    @10
    @9
    @11
    @5
    @8
    @2
    @21
    simp23r
    @23
    wn
    cR
    cP
    wne
    #
    cR
    cQ
    wne
    #
    wa
    #
    @22
    @10
    cR
    cP
    cR
    cQ
    neanior
    @22
    @26
    @10
    @22
    @26
    wa
    #
    cR
    cU
    cW
    c.le
    @27
    @20
    @9
    cP
    cR
    c.or
    co
    #
    cQ
    cR
    c.or
    co
    #
    wceq
    #
    cU
    cA
    wcel
    #
    cP
    cU
    c.or
    co
    #
    cQ
    cU
    c.or
    co
    #
    wceq
    #
    cR
    cU
    wceq
    #
    @14
    @15
    @20
    @2
    @13
    @26
    simpl33
    @22
    @9
    @26
    @9
    @11
    @5
    @8
    @2
    @21
    simp23l
    adantr
    #
    @27
    @30
    @24
    @25
    @15
    @22
    @24
    @25
    simprl
    @22
    @24
    @25
    simprr
    @14
    @15
    @20
    @2
    @13
    @26
    simpl32
    @27
    cK
    clc
    wcel
    #
    @3
    @6
    @9
    @14
    @30
    @24
    @25
    @15
    w3a
    wb
    @27
    @0
    @37
    @0
    @1
    @13
    @21
    @26
    simpl1l
    cK
    hlcvl
    syl
    @22
    @3
    @26
    @3
    @4
    @8
    @12
    @2
    @21
    simp21l
    #
    adantr
    @22
    @6
    @26
    @6
    @7
    @5
    @12
    @2
    @21
    simp22l
    #
    adantr
    @36
    @14
    @15
    @20
    @2
    @13
    @26
    simpl31
    #
    cA
    cP
    cQ
    cR
    c.or
    cK
    c.le
    cdleme0.a
    cdleme0.l
    cdleme0.j
    cvlsupr2
    syl131anc
    mpbir3and
    @22
    @31
    @26
    @22
    @0
    @1
    @3
    @4
    @6
    @14
    @31
    @0
    @1
    @13
    @21
    simp1l
    @0
    @1
    @13
    @21
    simp1r
    @38
    @3
    @4
    @8
    @12
    @2
    @21
    simp21r
    @39
    @2
    @13
    @14
    @15
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
    cdleme0.l
    cdleme0.j
    cdleme0.m
    cdleme0.a
    cdleme0.h
    cdleme0.u
    lhpat2
    syl222anc
    adantr
    @27
    @2
    @5
    @8
    @14
    @34
    @2
    @13
    @21
    @26
    simpl1
    #
    @5
    @8
    @12
    @2
    @21
    @26
    simpl21
    #
    @5
    @8
    @12
    @2
    @21
    @26
    simpl22
    #
    @40
    @2
    @5
    @8
    wa
    @14
    w3a
    #
    @34
    cU
    cW
    c.le
    wbr
    #
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
    cdleme0.l
    cdleme0.j
    cdleme0.m
    cdleme0.a
    cdleme0.h
    cdleme0.u
    cdleme02N
    #
    simpld
    syl121anc
    @20
    @19
    vr
    cA
    wrmo
    @9
    @30
    wa
    @31
    @34
    wa
    @35
    @19
    vr
    cA
    df-rmo
    @19
    @30
    @34
    vr
    cA
    cR
    cU
    @16
    cR
    wceq
    @17
    @28
    @18
    @29
    @16
    cR
    cP
    c.or
    oveq2
    @16
    cR
    cQ
    c.or
    oveq2
    eqeq12d
    @16
    cU
    wceq
    @17
    @32
    @18
    @33
    @16
    cU
    cP
    c.or
    oveq2
    @16
    cU
    cQ
    c.or
    oveq2
    eqeq12d
    rmoi
    syl3an1br
    syl122anc
    @27
    @2
    @5
    @8
    @14
    @45
    @41
    @42
    @43
    @40
    @44
    @34
    @45
    @46
    simprd
    syl121anc
    eqbrtrd
    ex
    syl5bir
    mt3d
end
