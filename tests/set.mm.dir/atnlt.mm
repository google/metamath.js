include "cal.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "pltirr.mm"
include "3adant3.mm"
include "breq2.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "cple.mm"
include "cfv.mm"
include "eqid.mm"
include "pltle.mm"
include "atcmp.mm"
include "sylibd.mm"
include "necon3ad.mm"
include "pm2.61dne.mm"

theorem atnlt
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.lt: class .<
  let cK: class K
  assume atnlt.s: |- .< = ( lt ` K )
  assume atnlt.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. AtLat /\ P e. A /\ Q e. A ) -> -. P .< Q )

  proof
    cK
    cal
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
    #
    cP
    cQ
    c.lt
    wbr
    #
    wn
    #
    cP
    cQ
    @3
    cP
    cP
    c.lt
    wbr
    #
    wn
    #
    cP
    cQ
    wceq
    #
    @5
    @0
    @1
    @7
    @2
    cal
    cA
    c.lt
    cK
    cP
    atnlt.s
    pltirr
    3adant3
    @8
    @6
    @4
    cP
    cQ
    cP
    c.lt
    breq2
    notbid
    syl5ibcom
    @3
    @4
    cP
    cQ
    @3
    @4
    cP
    cQ
    cK
    cple
    cfv
    #
    wbr
    @8
    cal
    cA
    cA
    c.lt
    cK
    @9
    cP
    cQ
    @9
    eqid
    #
    atnlt.s
    pltle
    cA
    cP
    cQ
    cK
    @9
    @10
    atnlt.a
    atcmp
    sylibd
    necon3ad
    pm2.61dne
end
