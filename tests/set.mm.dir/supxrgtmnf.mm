include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wcel.mm"
include "cpnf.mm"
include "wceq.mm"
include "wo.mm"
include "cmnf.mm"
include "wbr.mm"
include "wn.mm"
include "supxrbnd.mm"
include "3expia.mm"
include "con3d.mm"
include "wb.mm"
include "ressxr.mm"
include "sstr.mm"
include "mpan2.mm"
include "supxrcl.mm"
include "syl.mm"
include "adantr.mm"
include "nltpnft.mm"
include "sylibrd.mm"
include "orrd.mm"
include "mnfltxr.mm"

theorem supxrgtmnf
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B


  assert |- ( ( A C_ RR /\ A =/= (/) ) -> -oo < sup ( A , RR* , < ) )

  proof
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    wa
    #
    cA
    cxr
    clt
    csup
    #
    cr
    wcel
    #
    @3
    cpnf
    wceq
    #
    wo
    cmnf
    @3
    clt
    wbr
    @2
    @4
    @5
    @2
    @4
    wn
    @3
    cpnf
    clt
    wbr
    #
    wn
    #
    @5
    @2
    @6
    @4
    @0
    @1
    @6
    @4
    cA
    supxrbnd
    3expia
    con3d
    @2
    @3
    cxr
    wcel
    #
    @5
    @7
    wb
    @0
    @8
    @1
    @0
    cA
    cxr
    wss
    #
    @8
    @0
    cr
    cxr
    wss
    @9
    ressxr
    cA
    cr
    cxr
    sstr
    mpan2
    cA
    supxrcl
    syl
    adantr
    @3
    nltpnft
    syl
    sylibrd
    orrd
    @3
    mnfltxr
    syl
end
