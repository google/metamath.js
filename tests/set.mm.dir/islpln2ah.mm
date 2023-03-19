include "wcel.mm"
include "co.mm"
include "chlt.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "eleq1i.mm"
include "islpln2a.mm"
include "syl5bb.mm"

theorem islpln2ah
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


  assert |- ( ( K e. HL /\ ( Q e. A /\ R e. A /\ S e. A ) ) -> ( Y e. P <-> ( Q =/= R /\ -. S .<_ ( Q .\/ R ) ) ) )

  proof
    cY
    cP
    wcel
    cQ
    cR
    c.or
    co
    #
    cS
    c.or
    co
    #
    cP
    wcel
    cK
    chlt
    wcel
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
    wa
    cQ
    cR
    wne
    cS
    @0
    c.le
    wbr
    wn
    wa
    cY
    @1
    cP
    islpln2a.y
    eleq1i
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    c.le
    islpln2a.l
    islpln2a.j
    islpln2a.a
    islpln2a.p
    islpln2a
    syl5bb
end
