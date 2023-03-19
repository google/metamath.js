include "chlt.mm"
include "wcel.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "4atexlemk.mm"
include "4atexlemp.mm"
include "4atexlemq.mm"
include "4atexlems.mm"
include "4atexlemnslpq.mm"
include "4atlem0be.mm"
include "syl131anc.mm"

theorem 4atexlempns
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
  let cV: class V
  let cW: class W
  assume 4thatlem.ph: |- ( ph <-> ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( S e. A /\ ( R e. A /\ -. R .<_ W /\ ( P .\/ R ) = ( Q .\/ R ) ) /\ ( T e. A /\ ( U .\/ T ) = ( V .\/ T ) ) ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) ) ) )
  assume 4thatlemslps.l: |- .<_ = ( le ` K )
  assume 4thatlemslps.j: |- .\/ = ( join ` K )
  assume 4thatlemslps.a: |- A = ( Atoms ` K )


  assert |- ( ph -> P =/= S )

  proof
    wph
    cK
    chlt
    wcel
    cP
    cA
    wcel
    cQ
    cA
    wcel
    cS
    cA
    wcel
    cS
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    cP
    cS
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
    4atexlemnslpq
    cA
    cP
    cQ
    cS
    c.or
    cK
    c.le
    4thatlemslps.l
    4thatlemslps.j
    4thatlemslps.a
    4atlem0be
    syl131anc
end
