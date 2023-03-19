include "wcel.mm"
include "cvv.mm"
include "cfv.mm"
include "cid.mm"
include "wceq.mm"
include "wa.mm"
include "fvmptg.mm"
include "fvi.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "wn.mm"
include "c0.mm"
include "cdm.mm"
include "cv.mm"
include "eleq1d.mm"
include "dmmpt.mm"
include "elrab2.mm"
include "baib.mm"
include "notbid.mm"
include "ndmfv.mm"
include "syl6bir.mm"
include "imp.mm"
include "fvprc.mm"
include "pm2.61dan.mm"

theorem fvmpti
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vy: setvar y
  assume fvmptg.1: |- ( x = A -> B = C )
  assume fvmptg.2: |- F = ( x e. D |-> B )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint D y
  assert |- ( A e. D -> ( F ` A ) = ( _I ` C ) )

  proof
    cA
    cD
    wcel
    #
    cC
    cvv
    wcel
    #
    cA
    cF
    cfv
    #
    cC
    cid
    cfv
    #
    wceq
    @0
    @1
    wa
    @2
    cC
    @3
    vx
    cA
    cB
    cC
    cD
    cvv
    cF
    fvmptg.1
    fvmptg.2
    fvmptg
    @1
    @3
    cC
    wceq
    @0
    cC
    cvv
    fvi
    adantl
    eqtr4d
    @0
    @1
    wn
    #
    wa
    @2
    c0
    @3
    @0
    @4
    @2
    c0
    wceq
    #
    @0
    @4
    cA
    cF
    cdm
    #
    wcel
    #
    wn
    @5
    @0
    @7
    @1
    @7
    @0
    @1
    cB
    cvv
    wcel
    @1
    vx
    cA
    cD
    @6
    vx
    cv
    cA
    wceq
    cB
    cC
    cvv
    fvmptg.1
    eleq1d
    vx
    cD
    cB
    cF
    fvmptg.2
    dmmpt
    elrab2
    baib
    notbid
    cA
    cF
    ndmfv
    syl6bir
    imp
    @4
    @3
    c0
    wceq
    @0
    cC
    cid
    fvprc
    adantl
    eqtr4d
    pm2.61dan
end
