include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cmpt.mm"
include "wfun.mm"
include "cdm.mm"
include "funmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "ctex.mm"
include "eqid.mm"
include "dmmptss.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "domtr.mm"
include "mpancom.mm"
include "wfn.mm"
include "funfn.mm"
include "fnct.mm"
include "sylanb.mm"
include "sylancr.mm"

theorem mptct
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  assert |- ( A ~<_ _om -> ( x e. A |-> B ) ~<_ _om )

  proof
    cA
    com
    cdom
    wbr
    #
    vx
    cA
    cB
    cmpt
    #
    wfun
    #
    @1
    cdm
    #
    com
    cdom
    wbr
    #
    @1
    com
    cdom
    wbr
    #
    vx
    cA
    cB
    funmpt
    @3
    cA
    cdom
    wbr
    #
    @0
    @4
    @0
    cA
    cvv
    wcel
    @3
    cA
    wss
    @6
    cA
    ctex
    vx
    cA
    cB
    @1
    @1
    eqid
    dmmptss
    @3
    cA
    cvv
    ssdomg
    mpisyl
    @3
    cA
    com
    domtr
    mpancom
    @2
    @1
    @3
    wfn
    @4
    @5
    @1
    funfn
    @3
    @1
    fnct
    sylanb
    sylancr
end
