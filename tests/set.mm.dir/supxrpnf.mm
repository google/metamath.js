include "cxr.mm"
include "wss.mm"
include "cpnf.mm"
include "wcel.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cr.mm"
include "wa.mm"
include "csup.mm"
include "wceq.mm"
include "ssel.mm"
include "pnfnlt.mm"
include "syl6.mm"
include "ralrimiv.mm"
include "breq2.mm"
include "rspcev.mm"
include "ex.mm"
include "ralrimivw.mm"
include "anim12i.mm"
include "pnfxr.mm"
include "supxr.mm"
include "mpanl2.mm"
include "syldan.mm"

theorem supxrpnf
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B


  assert |- ( ( A C_ RR* /\ +oo e. A ) -> sup ( A , RR* , < ) = +oo )

  proof
    cA
    cxr
    wss
    #
    cpnf
    cA
    wcel
    #
    cpnf
    vy
    cv
    #
    clt
    wbr
    wn
    #
    vy
    cA
    wral
    #
    @2
    cpnf
    clt
    wbr
    #
    @2
    vz
    cv
    #
    clt
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cr
    wral
    #
    wa
    #
    cA
    cxr
    clt
    csup
    cpnf
    wceq
    #
    @0
    @4
    @1
    @10
    @0
    @3
    vy
    cA
    @0
    @2
    cA
    wcel
    @2
    cxr
    wcel
    @3
    cA
    cxr
    @2
    ssel
    @2
    pnfnlt
    syl6
    ralrimiv
    @1
    @9
    vy
    cr
    @1
    @5
    @8
    @7
    @5
    vz
    cpnf
    cA
    @6
    cpnf
    @2
    clt
    breq2
    rspcev
    ex
    ralrimivw
    anim12i
    @0
    cpnf
    cxr
    wcel
    @11
    @12
    pnfxr
    vy
    vz
    cA
    cpnf
    supxr
    mpanl2
    syldan
end
