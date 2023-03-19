include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "adantl.mm"
include "wb.mm"
include "ispointN.mm"
include "adantr.mm"
include "mpbird.mm"

theorem atpointN
  let cA: class A
  let cD: class D
  let cP: class P
  let cK: class K
  let cX: class X
  let va: setvar a
  let vx: setvar x
  assume ispoint.a: |- A = ( Atoms ` K )
  assume ispoint.p: |- P = ( Points ` K )


  assert |- ( ( K e. D /\ X e. A ) -> { X } e. P )

  proof
    cK
    cD
    wcel
    #
    cX
    cA
    wcel
    #
    wa
    cX
    csn
    #
    cP
    wcel
    #
    @2
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    cA
    wrex
    #
    @1
    @7
    @0
    @1
    @2
    @2
    wceq
    #
    @7
    @2
    eqid
    @6
    @8
    vx
    cX
    cA
    @4
    cX
    wceq
    @5
    @2
    @2
    @4
    cX
    sneq
    eqeq2d
    rspcev
    mpan2
    adantl
    @0
    @3
    @7
    wb
    @1
    cA
    cD
    cP
    cK
    @2
    vx
    ispoint.a
    ispoint.p
    ispointN
    adantr
    mpbird
end
