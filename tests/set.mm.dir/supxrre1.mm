include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wcel.mm"
include "cmnf.mm"
include "wbr.mm"
include "cpnf.mm"
include "wb.mm"
include "ressxr.mm"
include "sstr.mm"
include "mpan2.mm"
include "supxrcl.mm"
include "xrrebnd.mm"
include "3syl.mm"
include "adantr.mm"
include "supxrgtmnf.mm"
include "biantrurd.mm"
include "bitr4d.mm"

theorem supxrre1
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B


  assert |- ( ( A C_ RR /\ A =/= (/) ) -> ( sup ( A , RR* , < ) e. RR <-> sup ( A , RR* , < ) < +oo ) )

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
    cmnf
    @3
    clt
    wbr
    #
    @3
    cpnf
    clt
    wbr
    #
    wa
    #
    @6
    @0
    @4
    @7
    wb
    #
    @1
    @0
    cA
    cxr
    wss
    #
    @3
    cxr
    wcel
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
    @3
    xrrebnd
    3syl
    adantr
    @2
    @5
    @6
    cA
    supxrgtmnf
    biantrurd
    bitr4d
end
