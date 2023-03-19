include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "co.mm"
include "lhpat.mm"
include "syl5eqel.mm"

theorem lhpat2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume lhpat.l: |- .<_ = ( le ` K )
  assume lhpat.j: |- .\/ = ( join ` K )
  assume lhpat.m: |- ./\ = ( meet ` K )
  assume lhpat.a: |- A = ( Atoms ` K )
  assume lhpat.h: |- H = ( LHyp ` K )
  assume lhpat2.r: |- R = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ P =/= Q ) ) -> R e. A )

  proof
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
    cP
    cQ
    wne
    wa
    w3a
    cR
    cP
    cQ
    c.or
    co
    cW
    c.an
    co
    cA
    lhpat2.r
    cA
    cP
    cQ
    cH
    c.or
    cK
    c.le
    c.an
    cW
    lhpat.l
    lhpat.j
    lhpat.m
    lhpat.a
    lhpat.h
    lhpat
    syl5eqel
end
