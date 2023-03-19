include "wcel.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "ciin.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "cint.mm"
include "csn.mm"
include "cun.mm"
include "cvv.mm"
include "wceq.mm"
include "ssexg.mm"
include "expcom.mm"
include "ralimdv.mm"
include "imp.mm"
include "dfiin3g.mm"
include "syl.mm"
include "ineq2d.mm"
include "intun.mm"
include "intsng.mm"
include "adantr.mm"
include "ineq1d.mm"
include "syl5eq.mm"
include "eqtr4d.mm"

theorem riinint
  let cS: class S
  let vk: setvar k
  let cI: class I
  let cV: class V
  let cX: class X

  disjoint V k
  disjoint X k
  assert |- ( ( X e. V /\ A. k e. I S C_ X ) -> ( X i^i |^|_ k e. I S ) = |^| ( { X } u. ran ( k e. I |-> S ) ) )

  proof
    cX
    cV
    wcel
    #
    cS
    cX
    wss
    #
    vk
    cI
    wral
    #
    wa
    #
    cX
    vk
    cI
    cS
    ciin
    #
    cin
    cX
    vk
    cI
    cS
    cmpt
    crn
    #
    cint
    #
    cin
    #
    cX
    csn
    #
    @5
    cun
    cint
    #
    @3
    @4
    @6
    cX
    @3
    cS
    cvv
    wcel
    #
    vk
    cI
    wral
    #
    @4
    @6
    wceq
    @0
    @2
    @11
    @0
    @1
    @10
    vk
    cI
    @1
    @0
    @10
    cS
    cX
    cV
    ssexg
    expcom
    ralimdv
    imp
    vk
    cI
    cS
    cvv
    dfiin3g
    syl
    ineq2d
    @3
    @9
    @8
    cint
    #
    @6
    cin
    @7
    @8
    @5
    intun
    @3
    @12
    cX
    @6
    @0
    @12
    cX
    wceq
    @2
    cX
    cV
    intsng
    adantr
    ineq1d
    syl5eq
    eqtr4d
end
