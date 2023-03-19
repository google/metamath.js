include "cal.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "atcmp.mm"
include "necon3bbid.mm"

theorem atncmp
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cK: class K
  let c.le: class .<_
  assume atcmp.l: |- .<_ = ( le ` K )
  assume atcmp.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. AtLat /\ P e. A /\ Q e. A ) -> ( -. P .<_ Q <-> P =/= Q ) )

  proof
    cK
    cal
    wcel
    cP
    cA
    wcel
    cQ
    cA
    wcel
    w3a
    cP
    cQ
    c.le
    wbr
    cP
    cQ
    cA
    cP
    cQ
    cK
    c.le
    atcmp.l
    atcmp.a
    atcmp
    necon3bbid
end
