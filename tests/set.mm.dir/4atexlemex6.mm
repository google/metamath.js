include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wne.mm"
include "cv.mm"
include "wrex.mm"
include "simp11l.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13l.mm"
include "simp32.mm"
include "lhpat.mm"
include "syl112anc.mm"
include "simp2r.mm"
include "simp12l.mm"
include "simp33.mm"
include "atnlej1.mm"
include "syl131anc.mm"
include "necomd.mm"
include "hlsupr2.mm"
include "syl3anc.mm"
include "simp111.mm"
include "simp112.mm"
include "simp113.mm"
include "simp12r.mm"
include "simp2ll.mm"
include "3ad2ant1.mm"
include "simp2lr.mm"
include "simp131.mm"
include "3jca.mm"
include "3simpc.mm"
include "simp132.mm"
include "simp133.mm"
include "biid.mm"
include "eqid.mm"
include "4atexlemex4.mm"
include "4atexlemex2.mm"
include "pm2.61dane.mm"
include "syl332anc.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem 4atexlemex6
  let vz: setvar z
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vt: setvar t
  assume 4thatleme.l: |- .<_ = ( le ` K )
  assume 4thatleme.j: |- .\/ = ( join ` K )
  assume 4thatleme.m: |- ./\ = ( meet ` K )
  assume 4thatleme.a: |- A = ( Atoms ` K )
  assume 4thatleme.h: |- H = ( LHyp ` K )

  disjoint A z
  disjoint .\/ z
  disjoint .<_ z
  disjoint ./\ z
  disjoint P z
  disjoint Q z
  disjoint R z
  disjoint S z
  disjoint W z
  disjoint t z
  disjoint A t
  disjoint H t
  disjoint .\/ t
  disjoint K t
  disjoint .<_ t
  disjoint ./\ t
  disjoint P t
  disjoint Q t
  disjoint R t
  disjoint S t
  disjoint W t
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ S e. A ) /\ ( ( P .\/ R ) = ( Q .\/ R ) /\ P =/= Q /\ -. S .<_ ( P .\/ Q ) ) ) -> E. z e. A ( -. z .<_ W /\ ( P .\/ z ) = ( S .\/ z ) ) )

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
    wa
    #
    cP
    cR
    c.or
    co
    cQ
    cR
    c.or
    co
    wceq
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
    w3a
    #
    w3a
    #
    @17
    cW
    c.an
    co
    #
    vt
    cv
    #
    c.or
    co
    cP
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    @22
    c.or
    co
    wceq
    #
    vt
    cA
    wrex
    #
    vz
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @27
    c.or
    co
    cS
    @27
    c.or
    co
    wceq
    wa
    vz
    cA
    wrex
    #
    @20
    @0
    @21
    cA
    wcel
    #
    @24
    cA
    wcel
    #
    @26
    @0
    @1
    @5
    @8
    @14
    @19
    simp11l
    #
    @20
    @2
    @5
    @6
    @16
    @29
    @2
    @5
    @8
    @14
    @19
    simp11
    #
    @2
    @5
    @8
    @14
    @19
    simp12
    #
    @6
    @7
    @2
    @5
    @14
    @19
    simp13l
    #
    @9
    @14
    @15
    @16
    @18
    simp32
    cA
    cP
    cQ
    cH
    c.or
    cK
    c.le
    c.an
    cW
    4thatleme.l
    4thatleme.j
    4thatleme.m
    4thatleme.a
    4thatleme.h
    lhpat
    syl112anc
    @20
    @2
    @5
    @13
    cP
    cS
    wne
    @30
    @32
    @33
    @9
    @12
    @13
    @19
    simp2r
    #
    @20
    cS
    cP
    @20
    @0
    @13
    @3
    @6
    @18
    cS
    cP
    wne
    @31
    @35
    @3
    @4
    @2
    @8
    @14
    @19
    simp12l
    @34
    @9
    @14
    @15
    @16
    @18
    simp33
    cA
    cS
    cP
    cQ
    c.or
    cK
    c.le
    4thatleme.l
    4thatleme.j
    4thatleme.a
    atnlej1
    syl131anc
    necomd
    cA
    cP
    cS
    cH
    c.or
    cK
    c.le
    c.an
    cW
    4thatleme.l
    4thatleme.j
    4thatleme.m
    4thatleme.a
    4thatleme.h
    lhpat
    syl112anc
    cA
    @21
    @24
    c.or
    cK
    vt
    4thatleme.j
    4thatleme.a
    hlsupr2
    syl3anc
    @20
    @25
    @28
    vt
    cA
    @20
    @22
    cA
    wcel
    #
    @25
    w3a
    #
    @2
    @5
    @8
    @13
    @10
    @11
    @15
    w3a
    #
    @36
    @25
    wa
    #
    @16
    @18
    @28
    @2
    @5
    @8
    @14
    @19
    @36
    @25
    simp111
    @2
    @5
    @8
    @14
    @19
    @36
    @25
    simp112
    @2
    @5
    @8
    @14
    @19
    @36
    @25
    simp113
    @12
    @13
    @9
    @19
    @36
    @25
    simp12r
    @37
    @10
    @11
    @15
    @20
    @36
    @10
    @25
    @10
    @11
    @13
    @9
    @19
    simp2ll
    3ad2ant1
    @20
    @36
    @11
    @25
    @10
    @11
    @13
    @9
    @19
    simp2lr
    3ad2ant1
    @15
    @16
    @18
    @9
    @14
    @36
    @25
    simp131
    3jca
    @20
    @36
    @25
    3simpc
    @15
    @16
    @18
    @9
    @14
    @36
    @25
    simp132
    @15
    @16
    @18
    @9
    @14
    @36
    @25
    simp133
    @9
    @13
    @38
    @39
    w3a
    @16
    @18
    wa
    w3a
    #
    @28
    cQ
    @22
    c.or
    co
    @23
    c.an
    co
    #
    cS
    @40
    vz
    cA
    @41
    cR
    @22
    c.or
    co
    @23
    c.an
    co
    #
    cP
    cQ
    cR
    cS
    @22
    @21
    cH
    c.or
    cK
    c.le
    c.an
    @24
    cW
    @40
    biid
    #
    4thatleme.l
    4thatleme.j
    4thatleme.m
    4thatleme.a
    4thatleme.h
    @21
    eqid
    #
    @24
    eqid
    #
    @41
    eqid
    #
    @42
    eqid
    4atexlemex4
    @40
    vz
    cA
    @41
    cP
    cQ
    cR
    cS
    @22
    @21
    cH
    c.or
    cK
    c.le
    c.an
    @24
    cW
    @43
    4thatleme.l
    4thatleme.j
    4thatleme.m
    4thatleme.a
    4thatleme.h
    @44
    @45
    @46
    4atexlemex2
    pm2.61dane
    syl332anc
    rexlimdv3a
    mpd
end
