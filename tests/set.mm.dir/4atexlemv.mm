include "chlt.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wne.mm"
include "4atexlemk.mm"
include "4atexlemw.mm"
include "4atexlempw.mm"
include "4atexlems.mm"
include "4atexlempns.mm"
include "lhpat2.mm"
include "syl212anc.mm"

theorem 4atexlemv
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


  assert |- ( ph -> V e. A )

  proof
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cS
    cA
    wcel
    cP
    cS
    wne
    cV
    cA
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
    cV
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
    4thatlem0.v
    lhpat2
    syl212anc
end
