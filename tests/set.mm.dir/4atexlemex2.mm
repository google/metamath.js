include "wne.mm"
include "wa.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "4atexlemc.mm"
include "adantr.mm"
include "4atexlemnclw.mm"
include "4atexlemntlpq.mm"
include "id.mm"
include "syl5eqr.mm"
include "adantl.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "4atexlemkl.mm"
include "4atexlemqtb.mm"
include "4atexlempsb.mm"
include "eqid.mm"
include "latmle1.mm"
include "syl3anc.mm"
include "chlt.mm"
include "4atexlemk.mm"
include "4atexlemq.mm"
include "4atexlemt.mm"
include "hlatjcom.mm"
include "breqtrd.mm"
include "eqbrtrrd.mm"
include "wi.mm"
include "clc.mm"
include "4atexlemkc.mm"
include "4atexlemp.mm"
include "4atexlempnq.mm"
include "cvlatexch2.mm"
include "syl131anc.mm"
include "mpd.mm"
include "ex.mm"
include "necon3bd.mm"
include "simpr.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "w3a.mm"
include "wb.mm"
include "4atexlems.mm"
include "4atexlempns.mm"
include "cvlsupr2.mm"
include "mpbir3and.mm"
include "breq1.mm"
include "notbid.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"

theorem 4atexlemex2
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cC: class C
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
  assume 4thatlem0.c: |- C = ( ( Q .\/ T ) ./\ ( P .\/ S ) )

  disjoint A z
  disjoint C z
  disjoint .\/ z
  disjoint .<_ z
  disjoint P z
  disjoint S z
  disjoint W z
  assert |- ( ( ph /\ C =/= S ) -> E. z e. A ( -. z .<_ W /\ ( P .\/ z ) = ( S .\/ z ) ) )

  proof
    wph
    cC
    cS
    wne
    #
    wa
    #
    cC
    cA
    wcel
    #
    cC
    cW
    c.le
    wbr
    #
    wn
    #
    cP
    cC
    c.or
    co
    #
    cS
    cC
    c.or
    co
    #
    wceq
    #
    vz
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    cP
    @8
    c.or
    co
    #
    cS
    @8
    c.or
    co
    #
    wceq
    #
    wa
    #
    vz
    cA
    wrex
    wph
    @2
    @0
    wph
    cA
    cC
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
    4thatlem0.c
    4atexlemc
    #
    adantr
    wph
    @4
    @0
    wph
    cA
    cC
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
    4thatlem0.c
    4atexlemnclw
    adantr
    @1
    @7
    cC
    cP
    wne
    #
    @0
    cC
    cP
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    wph
    @16
    @0
    wph
    cT
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    wn
    @16
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
    4atexlemntlpq
    wph
    @19
    cC
    cP
    wph
    cC
    cP
    wceq
    #
    @19
    wph
    @20
    wa
    #
    cP
    cT
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    @19
    @21
    cQ
    cT
    c.or
    co
    #
    @17
    c.an
    co
    #
    cP
    @22
    c.le
    @20
    @25
    cP
    wceq
    wph
    @20
    @25
    cC
    cP
    4thatlem0.c
    @20
    id
    syl5eqr
    adantl
    wph
    @25
    @22
    c.le
    wbr
    @20
    wph
    @25
    @24
    @22
    c.le
    wph
    cK
    clat
    wcel
    #
    @24
    cK
    cbs
    cfv
    #
    wcel
    #
    @17
    @27
    wcel
    #
    @25
    @24
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
    4atexlemqtb
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
    @27
    cK
    c.le
    c.an
    @24
    @17
    @27
    eqid
    #
    4thatlem0.l
    4thatlem0.m
    latmle1
    syl3anc
    wph
    cK
    chlt
    wcel
    cQ
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    @24
    @22
    wceq
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
    #
    cA
    c.or
    cK
    cQ
    cT
    4thatlem0.j
    4thatlem0.a
    hlatjcom
    syl3anc
    breqtrd
    adantr
    eqbrtrrd
    wph
    @23
    @19
    wi
    #
    @20
    wph
    cK
    clc
    wcel
    #
    cP
    cA
    wcel
    #
    @35
    @34
    cP
    cQ
    wne
    @38
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
    @37
    @36
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
    cA
    cP
    cT
    cQ
    c.or
    cK
    c.le
    4thatlem0.l
    4thatlem0.j
    4thatlem0.a
    cvlatexch2
    syl131anc
    adantr
    mpd
    ex
    necon3bd
    mpd
    adantr
    wph
    @0
    simpr
    wph
    @18
    @0
    wph
    cC
    @25
    @17
    c.le
    4thatlem0.c
    wph
    @26
    @28
    @29
    @25
    @17
    c.le
    wbr
    @30
    @31
    @32
    @27
    cK
    c.le
    c.an
    @24
    @17
    @33
    4thatlem0.l
    4thatlem0.m
    latmle2
    syl3anc
    syl5eqbr
    adantr
    wph
    @7
    @16
    @0
    @18
    w3a
    wb
    #
    @0
    wph
    @39
    @40
    cS
    cA
    wcel
    @2
    cP
    cS
    wne
    @43
    @41
    @42
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
    @15
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
    4thatlem0.l
    4thatlem0.j
    4thatlem0.a
    4atexlempns
    cA
    cP
    cS
    cC
    c.or
    cK
    c.le
    4thatlem0.a
    4thatlem0.l
    4thatlem0.j
    cvlsupr2
    syl131anc
    adantr
    mpbir3and
    @14
    @4
    @7
    wa
    vz
    cC
    cA
    @8
    cC
    wceq
    #
    @10
    @4
    @13
    @7
    @44
    @9
    @3
    @8
    cC
    cW
    c.le
    breq1
    notbid
    @44
    @11
    @5
    @12
    @6
    @8
    cC
    cP
    c.or
    oveq2
    @8
    cC
    cS
    c.or
    oveq2
    eqeq12d
    anbi12d
    rspcev
    syl12anc
end
