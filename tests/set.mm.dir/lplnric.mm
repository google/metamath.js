include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "islpln2ah.mm"
include "biimp3a.mm"
include "simprd.mm"

theorem lplnric
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cY: class Y
  assume islpln2a.l: |- .<_ = ( le ` K )
  assume islpln2a.j: |- .\/ = ( join ` K )
  assume islpln2a.a: |- A = ( Atoms ` K )
  assume islpln2a.p: |- P = ( LPlanes ` K )
  assume islpln2a.y: |- Y = ( ( Q .\/ R ) .\/ S )


  assert |- ( ( K e. HL /\ ( Q e. A /\ R e. A /\ S e. A ) /\ Y e. P ) -> -. S .<_ ( Q .\/ R ) )

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
    c.le
    wbr
    wn
    #
    @0
    @1
    @2
    @3
    @4
    wa
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    c.le
    cY
    islpln2a.l
    islpln2a.j
    islpln2a.a
    islpln2a.p
    islpln2a.y
    islpln2ah
    biimp3a
    simprd
end
