include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wne.mm"
include "simp3r.mm"
include "sylbi.mm"

theorem 4atexlemnslpq
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


  assert |- ( ph -> -. S .<_ ( P .\/ Q ) )

  proof
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    w3a
    #
    cS
    cA
    wcel
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    cP
    cR
    c.or
    co
    cQ
    cR
    c.or
    co
    wceq
    w3a
    cT
    cA
    wcel
    cU
    cT
    c.or
    co
    cV
    cT
    c.or
    co
    wceq
    wa
    w3a
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
    c.le
    wbr
    wn
    #
    wa
    w3a
    @3
    4thatlem.ph
    @0
    @1
    @2
    @3
    simp3r
    sylbi
end
