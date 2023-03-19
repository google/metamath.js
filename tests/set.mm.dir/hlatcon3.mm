include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "3noncolr2.mm"
include "simprd.mm"

theorem hlatcon3
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume 3noncol.l: |- .<_ = ( le ` K )
  assume 3noncol.j: |- .\/ = ( join ` K )
  assume 3noncol.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) ) ) -> -. P .<_ ( Q .\/ R ) )

  proof
    cK
    chlt
    wcel
    cP
    cA
    wcel
    cQ
    cA
    wcel
    cR
    cA
    wcel
    w3a
    cP
    cQ
    wne
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    wa
    w3a
    cQ
    cR
    wne
    cP
    cQ
    cR
    c.or
    co
    c.le
    wbr
    wn
    cA
    cP
    cQ
    cR
    c.or
    cK
    c.le
    3noncol.l
    3noncol.j
    3noncol.a
    3noncolr2
    simprd
end
