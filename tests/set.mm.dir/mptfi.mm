include "cfn.mm"
include "wcel.mm"
include "cmpt.mm"
include "cdm.mm"
include "wfn.mm"
include "wfun.mm"
include "funmpt.mm"
include "funfn.mm"
include "mpbi.mm"
include "wss.mm"
include "eqid.mm"
include "dmmptss.mm"
include "ssfi.mm"
include "mpan2.mm"
include "fnfi.mm"
include "sylancr.mm"

theorem mptfi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  assert |- ( A e. Fin -> ( x e. A |-> B ) e. Fin )

  proof
    cA
    cfn
    wcel
    #
    vx
    cA
    cB
    cmpt
    #
    @1
    cdm
    #
    wfn
    #
    @2
    cfn
    wcel
    #
    @1
    cfn
    wcel
    @1
    wfun
    @3
    vx
    cA
    cB
    funmpt
    @1
    funfn
    mpbi
    @0
    @2
    cA
    wss
    @4
    vx
    cA
    cB
    @1
    @1
    eqid
    dmmptss
    cA
    @2
    ssfi
    mpan2
    @2
    @1
    fnfi
    sylancr
end
