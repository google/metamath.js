include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "4atexlemnslpq.mm"
include "wceq.mm"
include "wa.mm"
include "chlt.mm"
include "wcel.mm"
include "4atexlemk.mm"
include "4atexlemp.mm"
include "4atexlems.mm"
include "hlatlej2.mm"
include "syl3anc.mm"
include "adantr.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "4atexlemkl.mm"
include "4atexlempsb.mm"
include "4atexlemwb.mm"
include "eqid.mm"
include "latmle1.mm"
include "syl5eqbr.mm"
include "clc.mm"
include "wb.mm"
include "4atexlemkc.mm"
include "4atexlemv.mm"
include "latmle2.mm"
include "4atexlempw.mm"
include "simprd.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "cvlatexchb1.mm"
include "syl131anc.mm"
include "mpbid.mm"
include "oveq2.mm"
include "eqcomd.mm"
include "4atexlemq.mm"
include "hlatjcl.mm"
include "4atexlemu.mm"
include "sylan9eqr.mm"
include "eqtr3d.mm"
include "breqtrd.mm"
include "ex.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem 4atexlemunv
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
  assume 4thatlem0.l: |- .<_ = ( le ` K )
  assume 4thatlem0.j: |- .\/ = ( join ` K )
  assume 4thatlem0.m: |- ./\ = ( meet ` K )
  assume 4thatlem0.a: |- A = ( Atoms ` K )
  assume 4thatlem0.h: |- H = ( LHyp ` K )
  assume 4thatlem0.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume 4thatlem0.v: |- V = ( ( P .\/ S ) ./\ W )


  assert |- ( ph -> U =/= V )

  proof
    wph
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
    cU
    cV
    wne
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
    @1
    cU
    cV
    wph
    cU
    cV
    wceq
    #
    @1
    wph
    @2
    wa
    #
    cS
    cP
    cS
    c.or
    co
    #
    @0
    c.le
    wph
    cS
    @4
    c.le
    wbr
    #
    @2
    wph
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    @5
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
    4atexlemk
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
    #
    cA
    cP
    cS
    c.or
    cK
    c.le
    4thatlem0.l
    4thatlem0.j
    4thatlem0.a
    hlatlej2
    syl3anc
    adantr
    @3
    cP
    cV
    c.or
    co
    #
    @4
    @0
    wph
    @12
    @4
    wceq
    #
    @2
    wph
    cV
    @4
    c.le
    wbr
    #
    @13
    wph
    cV
    @4
    cW
    c.an
    co
    #
    @4
    c.le
    4thatlem0.v
    wph
    cK
    clat
    wcel
    #
    @4
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @17
    wcel
    #
    @15
    @4
    c.le
    wbr
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
    4atexlemkl
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
    4thatlem0.j
    4thatlem0.a
    4atexlempsb
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
    4thatlem0.h
    4atexlemwb
    #
    @17
    cK
    c.le
    c.an
    @4
    cW
    @17
    eqid
    #
    4thatlem0.l
    4thatlem0.m
    latmle1
    syl3anc
    syl5eqbr
    wph
    cK
    clc
    wcel
    #
    cV
    cA
    wcel
    @8
    @7
    cV
    cP
    wne
    #
    @14
    @13
    wb
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
    c.an
    cV
    cW
    4thatlem.ph
    4thatlem0.l
    4thatlem0.j
    4thatlem0.m
    4thatlem0.a
    4thatlem0.h
    4thatlem0.u
    4thatlem0.v
    4atexlemv
    @11
    @10
    wph
    cV
    cW
    c.le
    wbr
    cP
    cW
    c.le
    wbr
    wn
    #
    @25
    wph
    cV
    @15
    cW
    c.le
    4thatlem0.v
    wph
    @16
    @18
    @19
    @15
    cW
    c.le
    wbr
    @20
    @21
    @22
    @17
    cK
    c.le
    c.an
    @4
    cW
    @23
    4thatlem0.l
    4thatlem0.m
    latmle2
    syl3anc
    syl5eqbr
    wph
    @7
    @27
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
    simprd
    #
    cV
    cP
    cW
    c.le
    nbrne2
    syl2anc
    cA
    cV
    cS
    cP
    c.or
    cK
    c.le
    4thatlem0.l
    4thatlem0.j
    4thatlem0.a
    cvlatexchb1
    syl131anc
    mpbid
    adantr
    @2
    wph
    @12
    cP
    cU
    c.or
    co
    #
    @0
    @2
    @29
    @12
    cU
    cV
    cP
    c.or
    oveq2
    eqcomd
    wph
    cU
    @0
    c.le
    wbr
    #
    @29
    @0
    wceq
    #
    wph
    cU
    @0
    cW
    c.an
    co
    #
    @0
    c.le
    4thatlem0.u
    wph
    @16
    @0
    @17
    wcel
    #
    @19
    @32
    @0
    c.le
    wbr
    @20
    wph
    @6
    @7
    cQ
    cA
    wcel
    #
    @33
    @9
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
    cA
    @17
    c.or
    cK
    cP
    cQ
    @23
    4thatlem0.j
    4thatlem0.a
    hlatjcl
    syl3anc
    #
    @22
    @17
    cK
    c.le
    c.an
    @0
    cW
    @23
    4thatlem0.l
    4thatlem0.m
    latmle1
    syl3anc
    syl5eqbr
    wph
    @24
    cU
    cA
    wcel
    @34
    @7
    cU
    cP
    wne
    #
    @30
    @31
    wb
    @26
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
    c.an
    cV
    cW
    4thatlem.ph
    4thatlem0.l
    4thatlem0.j
    4thatlem0.m
    4thatlem0.a
    4thatlem0.h
    4thatlem0.u
    4atexlemu
    @35
    @10
    wph
    cU
    cW
    c.le
    wbr
    @27
    @37
    wph
    cU
    @32
    cW
    c.le
    4thatlem0.u
    wph
    @16
    @33
    @19
    @32
    cW
    c.le
    wbr
    @20
    @36
    @22
    @17
    cK
    c.le
    c.an
    @0
    cW
    @23
    4thatlem0.l
    4thatlem0.m
    latmle2
    syl3anc
    syl5eqbr
    @28
    cU
    cP
    cW
    c.le
    nbrne2
    syl2anc
    cA
    cU
    cQ
    cP
    c.or
    cK
    c.le
    4thatlem0.l
    4thatlem0.j
    4thatlem0.a
    cvlatexchb1
    syl131anc
    mpbid
    sylan9eqr
    eqtr3d
    breqtrd
    ex
    necon3bd
    mpd
end
