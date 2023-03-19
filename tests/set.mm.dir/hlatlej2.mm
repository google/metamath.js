include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "hlatlej1.mm"
include "3com23.mm"
include "hlatjcom.mm"
include "breqtrrd.mm"

theorem hlatlej2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume hlatlej.l: |- .<_ = ( le ` K )
  assume hlatlej.j: |- .\/ = ( join ` K )
  assume hlatlej.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ P e. A /\ Q e. A ) -> Q .<_ ( P .\/ Q ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    w3a
    cQ
    cQ
    cP
    c.or
    co
    #
    cP
    cQ
    c.or
    co
    c.le
    @0
    @2
    @1
    cQ
    @3
    c.le
    wbr
    cA
    cQ
    cP
    c.or
    cK
    c.le
    hlatlej.l
    hlatlej.j
    hlatlej.a
    hlatlej1
    3com23
    cA
    c.or
    cK
    cP
    cQ
    hlatlej.j
    hlatlej.a
    hlatjcom
    breqtrrd
end
