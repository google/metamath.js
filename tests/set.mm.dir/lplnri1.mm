include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "eqid.mm"
include "islpln2ah.mm"
include "biimp3a.mm"
include "simpld.mm"

theorem lplnri1
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let cY: class Y
  assume lplnri1.j: |- .\/ = ( join ` K )
  assume lplnri1.a: |- A = ( Atoms ` K )
  assume lplnri1.p: |- P = ( LPlanes ` K )
  assume lplnri1.y: |- Y = ( ( Q .\/ R ) .\/ S )


  assert |- ( ( K e. HL /\ ( Q e. A /\ R e. A /\ S e. A ) /\ Y e. P ) -> Q =/= R )

  proof
    cK
    chlt
    wcel
    #
    cQ
    cA
    wcel
    cR
    cA
    wcel
    cS
    cA
    wcel
    w3a
    #
    cY
    cP
    wcel
    #
    w3a
    cQ
    cR
    wne
    #
    cS
    cQ
    cR
    c.or
    co
    cK
    cple
    cfv
    #
    wbr
    wn
    #
    @0
    @1
    @2
    @3
    @5
    wa
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    @4
    cY
    @4
    eqid
    lplnri1.j
    lplnri1.a
    lplnri1.p
    lplnri1.y
    islpln2ah
    biimp3a
    simpld
end
