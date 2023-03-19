include "wcel.mm"
include "co.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "wrex.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "psubspi.mm"
include "sylan2.mm"

theorem psubspi2N
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vk: setvar k
  let vr: setvar r
  let vs: setvar s
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  assume psubspset.l: |- .<_ = ( le ` K )
  assume psubspset.j: |- .\/ = ( join ` K )
  assume psubspset.a: |- A = ( Atoms ` K )
  assume psubspset.s: |- S = ( PSubSp ` K )


  assert |- ( ( ( K e. D /\ X e. S /\ P e. A ) /\ ( Q e. X /\ R e. X /\ P .<_ ( Q .\/ R ) ) ) -> P e. X )

  proof
    cQ
    cX
    wcel
    cR
    cX
    wcel
    cP
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    cK
    cD
    wcel
    cX
    cS
    wcel
    cP
    cA
    wcel
    w3a
    cP
    vq
    cv
    #
    vr
    cv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    vr
    cX
    wrex
    vq
    cX
    wrex
    cP
    cX
    wcel
    @5
    @1
    cP
    cQ
    @3
    c.or
    co
    #
    c.le
    wbr
    vq
    vr
    cQ
    cR
    cX
    cX
    @2
    cQ
    wceq
    @4
    @6
    cP
    c.le
    @2
    cQ
    @3
    c.or
    oveq1
    breq2d
    @3
    cR
    wceq
    @6
    @0
    cP
    c.le
    @3
    cR
    cQ
    c.or
    oveq2
    breq2d
    rspc2ev
    cA
    cD
    cP
    cS
    c.or
    cK
    c.le
    cX
    vr
    vq
    psubspset.l
    psubspset.j
    psubspset.a
    psubspset.s
    psubspi
    sylan2
end
