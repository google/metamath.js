include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "eqid.mm"
include "4atexlemkl.mm"
include "wcel.mm"
include "4atexlemt.mm"
include "atbase.mm"
include "syl.mm"
include "chlt.mm"
include "4atexlemk.mm"
include "4atexlemu.mm"
include "4atexlemv.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "4atexlemwb.mm"
include "clc.mm"
include "wne.mm"
include "wceq.mm"
include "wbr.mm"
include "4atexlemkc.mm"
include "4atexlemunv.mm"
include "4atexlemutvt.mm"
include "cvlsupr4.mm"
include "syl132anc.mm"
include "clat.mm"
include "4atexlemp.mm"
include "4atexlemq.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "4atexlempsb.mm"
include "wa.mm"
include "wb.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "lattrd.mm"

theorem 4atexlemtlw
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


  assert |- ( ph -> T .<_ W )

  proof
    wph
    cK
    cbs
    cfv
    #
    cK
    c.le
    cT
    cU
    cV
    c.or
    co
    #
    cW
    @0
    eqid
    #
    4thatlem0.l
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
    cT
    cA
    wcel
    #
    cT
    @0
    wcel
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
    @0
    cT
    cK
    @2
    4thatlem0.a
    atbase
    syl
    wph
    cK
    chlt
    wcel
    #
    cU
    cA
    wcel
    #
    cV
    cA
    wcel
    #
    @1
    @0
    wcel
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
    #
    cA
    @0
    c.or
    cK
    cU
    cV
    @2
    4thatlem0.j
    4thatlem0.a
    hlatjcl
    syl3anc
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
    wph
    cK
    clc
    wcel
    @7
    @8
    @4
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
    cT
    @1
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
    4atexlemkc
    @10
    @11
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
    c.le
    4thatlem0.a
    4thatlem0.l
    4thatlem0.j
    cvlsupr4
    syl132anc
    wph
    cU
    cW
    c.le
    wbr
    #
    cV
    cW
    c.le
    wbr
    #
    @1
    cW
    c.le
    wbr
    #
    wph
    cU
    cP
    cQ
    c.or
    co
    #
    cW
    c.an
    co
    #
    cW
    c.le
    4thatlem0.u
    wph
    cK
    clat
    wcel
    #
    @16
    @0
    wcel
    #
    cW
    @0
    wcel
    #
    @17
    cW
    c.le
    wbr
    @3
    wph
    @6
    cP
    cA
    wcel
    cQ
    cA
    wcel
    @19
    @9
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
    cA
    @0
    c.or
    cK
    cP
    cQ
    @2
    4thatlem0.j
    4thatlem0.a
    hlatjcl
    syl3anc
    @12
    @0
    cK
    c.le
    c.an
    @16
    cW
    @2
    4thatlem0.l
    4thatlem0.m
    latmle2
    syl3anc
    syl5eqbr
    wph
    cV
    cP
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    cW
    c.le
    4thatlem0.v
    wph
    @18
    @21
    @0
    wcel
    @20
    @22
    cW
    c.le
    wbr
    @3
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
    @12
    @0
    cK
    c.le
    c.an
    @21
    cW
    @2
    4thatlem0.l
    4thatlem0.m
    latmle2
    syl3anc
    syl5eqbr
    wph
    @18
    cU
    @0
    wcel
    #
    cV
    @0
    wcel
    #
    @20
    @13
    @14
    wa
    @15
    wb
    @3
    wph
    @7
    @23
    @10
    cA
    @0
    cU
    cK
    @2
    4thatlem0.a
    atbase
    syl
    wph
    @8
    @24
    @11
    cA
    @0
    cV
    cK
    @2
    4thatlem0.a
    atbase
    syl
    @12
    @0
    c.or
    cK
    c.le
    cU
    cV
    cW
    @2
    4thatlem0.l
    4thatlem0.j
    latjle12
    syl13anc
    mpbi2and
    lattrd
end
