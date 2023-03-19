include "chlt.mm"
include "wcel.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "hllat.mm"
include "eqid.mm"
include "atbase.mm"
include "latlej1.mm"
include "syl3an.mm"

theorem hlatlej1
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume hlatlej.l: |- .<_ = ( le ` K )
  assume hlatlej.j: |- .\/ = ( join ` K )
  assume hlatlej.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ P e. A /\ Q e. A ) -> P .<_ ( P .\/ Q ) )

  proof
    cK
    chlt
    wcel
    cK
    clat
    wcel
    cP
    cA
    wcel
    cP
    cK
    cbs
    cfv
    #
    wcel
    cQ
    cA
    wcel
    cQ
    @0
    wcel
    cP
    cP
    cQ
    c.or
    co
    c.le
    wbr
    cK
    hllat
    cA
    @0
    cP
    cK
    @0
    eqid
    #
    hlatlej.a
    atbase
    cA
    @0
    cQ
    cK
    @1
    hlatlej.a
    atbase
    @0
    c.or
    cK
    c.le
    cP
    cQ
    @1
    hlatlej.l
    hlatlej.j
    latlej1
    syl3an
end
