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
include "crab.mm"
include "eqid.mm"
include "dmmpt.mm"
include "cv.mm"
include "wa.mm"
include "cab.mm"
include "df-rab.mm"
include "simpl.mm"
include "ss2abi.mm"
include "abid2f.mm"
include "sseqtri.mm"
include "eqsstri.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "domtr.mm"
include "mpancom.mm"
include "wfn.mm"
include "funfn.mm"
include "fnct.mm"
include "sylanb.mm"
include "sylancr.mm"

theorem mptctf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume mptctf.1: |- F/_ x A


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
    @3
    cB
    cvv
    wcel
    #
    vx
    cA
    crab
    #
    cA
    vx
    cA
    cB
    @1
    @1
    eqid
    dmmpt
    @8
    vx
    cv
    cA
    wcel
    #
    @7
    wa
    #
    vx
    cab
    #
    cA
    @7
    vx
    cA
    df-rab
    @11
    @9
    vx
    cab
    cA
    @10
    @9
    vx
    @9
    @7
    simpl
    ss2abi
    vx
    cA
    mptctf.1
    abid2f
    sseqtri
    eqsstri
    eqsstri
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
