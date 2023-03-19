include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "ccvr.mm"
include "cfv.mm"
include "eqid.mm"
include "atcvrj1.mm"
include "atcvrneN.mm"
include "syld3an3.mm"

theorem atleneN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume atlene.l: |- .<_ = ( le ` K )
  assume atlene.j: |- .\/ = ( join ` K )
  assume atlene.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( P =/= R /\ P .<_ ( Q .\/ R ) ) ) -> Q =/= R )

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
    cR
    wne
    cP
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    wa
    cP
    @0
    cK
    ccvr
    cfv
    #
    wbr
    cQ
    cR
    wne
    cA
    @1
    cP
    cQ
    cR
    c.or
    cK
    c.le
    atlene.l
    atlene.j
    @1
    eqid
    #
    atlene.a
    atcvrj1
    cA
    @1
    cP
    cQ
    cR
    c.or
    cK
    atlene.j
    @2
    atlene.a
    atcvrneN
    syld3an3
end
