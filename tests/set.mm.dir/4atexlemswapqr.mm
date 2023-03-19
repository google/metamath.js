include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wne.mm"
include "simp11.mm"
include "sylbi.mm"
include "4atexlempw.mm"
include "simp22.mm"
include "3simpa.mm"
include "syl.mm"
include "3jca.mm"
include "4atexlems.mm"
include "4atexlemq.mm"
include "simp13r.mm"
include "clc.mm"
include "4atexlemkc.mm"
include "4atexlemp.mm"
include "simpld.mm"
include "4atexlempnq.mm"
include "simp223.mm"
include "cvlsupr7.mm"
include "syl132anc.mm"
include "4atexlemt.mm"
include "cvlsupr8.mm"
include "oveq1d.mm"
include "syl5eq.mm"
include "4atexlemutvt.mm"
include "eqtr3d.mm"
include "jca.mm"
include "cvlsupr5.mm"
include "necomd.mm"
include "4atexlemnslpq.mm"
include "eqcomd.mm"
include "breq2d.mm"
include "mtbird.mm"

theorem 4atexlemswapqr
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume 4thatlem.ph: |- ( ph <-> ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( S e. A /\ ( R e. A /\ -. R .<_ W /\ ( P .\/ R ) = ( Q .\/ R ) ) /\ ( T e. A /\ ( U .\/ T ) = ( V .\/ T ) ) ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) ) ) )
  assume 4thatlemslps.l: |- .<_ = ( le ` K )
  assume 4thatlemslps.j: |- .\/ = ( join ` K )
  assume 4thatlemslps.a: |- A = ( Atoms ` K )
  assume 4thatlemsw.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ph -> ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( S e. A /\ ( Q e. A /\ -. Q .<_ W /\ ( P .\/ Q ) = ( R .\/ Q ) ) /\ ( T e. A /\ ( ( ( P .\/ R ) ./\ W ) .\/ T ) = ( V .\/ T ) ) ) /\ ( P =/= R /\ -. S .<_ ( P .\/ R ) ) ) )

  proof
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    wn
    #
    wa
    #
    w3a
    cS
    cA
    wcel
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
    cP
    cQ
    c.or
    co
    #
    cR
    cQ
    c.or
    co
    wceq
    #
    w3a
    #
    cT
    cA
    wcel
    #
    cP
    cR
    c.or
    co
    #
    cW
    c.an
    co
    #
    cT
    c.or
    co
    #
    cV
    cT
    c.or
    co
    #
    wceq
    #
    wa
    #
    w3a
    cP
    cR
    wne
    #
    cS
    @13
    c.le
    wbr
    #
    wn
    #
    wa
    wph
    @0
    @2
    @5
    wph
    @0
    @2
    @7
    @8
    wa
    #
    w3a
    #
    @6
    @3
    @4
    @13
    cQ
    cR
    c.or
    co
    wceq
    #
    w3a
    #
    @12
    cU
    cT
    c.or
    co
    #
    @16
    wceq
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cS
    @9
    c.le
    wbr
    #
    wn
    wa
    #
    w3a
    #
    @0
    4thatlem.ph
    @0
    @2
    @22
    @28
    @31
    simp11
    sylbi
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlempw
    wph
    @32
    @5
    4thatlem.ph
    @32
    @25
    @5
    @23
    @6
    @25
    @27
    @31
    simp22
    @3
    @4
    @24
    3simpa
    syl
    sylbi
    #
    3jca
    wph
    @6
    @11
    @18
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlems
    wph
    @7
    @8
    @10
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlemq
    #
    wph
    @32
    @8
    4thatlem.ph
    @7
    @8
    @0
    @2
    @28
    @31
    simp13r
    sylbi
    wph
    cK
    clc
    wcel
    #
    @1
    @7
    @3
    @29
    @24
    @10
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlemkc
    #
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlemp
    #
    @34
    wph
    @3
    @4
    @33
    simpld
    #
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlempnq
    #
    wph
    @32
    @24
    4thatlem.ph
    @3
    @4
    @24
    @6
    @27
    @23
    @31
    simp223
    sylbi
    #
    cA
    cP
    cQ
    cR
    c.or
    cK
    4thatlemslps.a
    4thatlemslps.j
    cvlsupr7
    syl132anc
    3jca
    wph
    @12
    @17
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlemt
    wph
    @26
    @15
    @16
    wph
    cU
    @14
    cT
    c.or
    wph
    cU
    @9
    cW
    c.an
    co
    @14
    4thatlemsw.u
    wph
    @9
    @13
    cW
    c.an
    wph
    @35
    @1
    @7
    @3
    @29
    @24
    @9
    @13
    wceq
    @36
    @37
    @34
    @38
    @39
    @40
    cA
    cP
    cQ
    cR
    c.or
    cK
    4thatlemslps.a
    4thatlemslps.j
    cvlsupr8
    syl132anc
    #
    oveq1d
    syl5eq
    oveq1d
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlemutvt
    eqtr3d
    jca
    3jca
    wph
    @19
    @21
    wph
    @35
    @1
    @7
    @3
    @29
    @24
    @19
    @36
    @37
    @34
    @38
    @39
    @40
    @35
    @1
    @7
    @3
    w3a
    @29
    @24
    wa
    w3a
    cR
    cP
    cA
    cP
    cQ
    cR
    c.or
    cK
    4thatlemslps.a
    4thatlemslps.j
    cvlsupr5
    necomd
    syl132anc
    wph
    @20
    @30
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlemnslpq
    wph
    @13
    @9
    cS
    c.le
    wph
    @9
    @13
    @41
    eqcomd
    breq2d
    mtbird
    jca
    3jca
end
