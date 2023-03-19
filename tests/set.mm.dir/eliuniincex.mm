include "wcel.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wb.mm"
include "cvv.mm"
include "nvel.mm"
include "eqneltri.mm"
include "c0.mm"
include "csn.mm"
include "0ex.mm"
include "snid.mm"
include "eleqtrri.mm"
include "ral0.mm"
include "nfcv.mm"
include "nfcxfr.mm"
include "nfel.mm"
include "nfral.mm"
include "cv.mm"
include "wceq.mm"
include "raleqi.mm"
include "a1i.mm"
include "rspce.mm"
include "mp2an.mm"
include "wa.mm"
include "wo.mm"
include "pm3.22.mm"
include "olcd.mm"
include "xor.mm"
include "sylibr.mm"

theorem eliuniincex
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cZ: class Z
  assume eliuniincex.1: |- B = { (/) }
  assume eliuniincex.2: |- C = (/)
  assume eliuniincex.3: |- D = (/)
  assume eliuniincex.4: |- Z = _V

  disjoint B x
  disjoint C y
  disjoint Z x
  assert |- -. ( Z e. A <-> E. x e. B A. y e. C Z e. D )

  proof
    cZ
    cA
    wcel
    #
    wn
    #
    cZ
    cD
    wcel
    #
    vy
    cC
    wral
    #
    vx
    cB
    wrex
    #
    @0
    @4
    wb
    wn
    #
    cZ
    cvv
    cA
    eliuniincex.4
    cA
    nvel
    eqneltri
    c0
    cB
    wcel
    @2
    vy
    c0
    wral
    #
    @4
    c0
    c0
    csn
    cB
    c0
    0ex
    snid
    eliuniincex.1
    eleqtrri
    @2
    vy
    ral0
    @3
    @6
    vx
    c0
    cB
    @2
    vx
    vy
    c0
    vx
    c0
    nfcv
    #
    vx
    cZ
    cD
    vx
    cZ
    nfcv
    vx
    cD
    c0
    eliuniincex.3
    @7
    nfcxfr
    nfel
    nfral
    @3
    @6
    wb
    vx
    cv
    c0
    wceq
    @2
    vy
    cC
    c0
    eliuniincex.2
    raleqi
    a1i
    rspce
    mp2an
    @1
    @4
    wa
    #
    @0
    @4
    wn
    wa
    #
    @4
    @1
    wa
    #
    wo
    @5
    @8
    @10
    @9
    @1
    @4
    pm3.22
    olcd
    @0
    @4
    xor
    sylibr
    mp2an
end
