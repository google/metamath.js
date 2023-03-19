include "co.mm"
include "wbr.mm"
include "4atexlemtlw.mm"
include "wn.mm"
include "wa.mm"
include "wne.mm"
include "clc.mm"
include "wcel.mm"
include "wceq.mm"
include "4atexlemkc.mm"
include "4atexlemu.mm"
include "4atexlemv.mm"
include "4atexlemt.mm"
include "4atexlemunv.mm"
include "4atexlemutvt.mm"
include "cvlsupr5.mm"
include "syl132anc.mm"
include "adantr.mm"
include "chlt.mm"
include "wb.mm"
include "4atexlemk.mm"
include "4atexlemw.mm"
include "jca.mm"
include "4atexlempw.mm"
include "4atexlemq.mm"
include "4atexlempnq.mm"
include "simpr.mm"
include "lhpat3.mm"
include "syl222anc.mm"
include "mpbird.mm"
include "ex.mm"
include "mt2d.mm"

theorem 4atexlemntlpq
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


  assert |- ( ph -> -. T .<_ ( P .\/ Q ) )

  proof
    wph
    cT
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    cT
    cW
    c.le
    wbr
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
    4atexlemtlw
    wph
    @0
    @1
    wn
    #
    wph
    @0
    wa
    #
    @2
    cT
    cU
    wne
    #
    wph
    @4
    @0
    wph
    cK
    clc
    wcel
    cU
    cA
    wcel
    cV
    cA
    wcel
    cT
    cA
    wcel
    #
    cU
    cV
    wne
    cU
    cT
    c.or
    co
    cV
    cT
    c.or
    co
    wceq
    @4
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
    4atexlemunv
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
    cA
    cU
    cV
    cT
    c.or
    cK
    4thatlem0.a
    4thatlem0.j
    cvlsupr5
    syl132anc
    adantr
    @3
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
    #
    @5
    cP
    cQ
    wne
    #
    @0
    @2
    @4
    wb
    wph
    @9
    @0
    wph
    @7
    @8
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
    4atexlemw
    jca
    adantr
    wph
    @10
    @0
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
    adantr
    wph
    @11
    @0
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
    adantr
    wph
    @5
    @0
    @6
    adantr
    wph
    @12
    @0
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
    adantr
    wph
    @0
    simpr
    cA
    cP
    cQ
    cU
    cT
    cH
    c.or
    cK
    c.le
    c.an
    cW
    4thatlem0.l
    4thatlem0.j
    4thatlem0.m
    4thatlem0.a
    4thatlem0.h
    4thatlem0.u
    lhpat3
    syl222anc
    mpbird
    ex
    mt2d
end
