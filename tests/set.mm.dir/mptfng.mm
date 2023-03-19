include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "cv.mm"
include "wceq.mm"
include "weu.mm"
include "wfn.mm"
include "eueq.mm"
include "ralbii.mm"
include "cmpt.mm"
include "wa.mm"
include "copab.mm"
include "df-mpt.mm"
include "eqtri.mm"
include "fnopabg.mm"
include "bitri.mm"

theorem mptfng
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  assume mptfng.1: |- F = ( x e. A |-> B )

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A. x e. A B e. _V <-> F Fn A )

  proof
    cB
    cvv
    wcel
    #
    vx
    cA
    wral
    vy
    cv
    cB
    wceq
    #
    vy
    weu
    #
    vx
    cA
    wral
    cF
    cA
    wfn
    @0
    @2
    vx
    cA
    vy
    cB
    eueq
    ralbii
    @1
    vx
    vy
    cA
    cF
    cF
    vx
    cA
    cB
    cmpt
    vx
    cv
    cA
    wcel
    @1
    wa
    vx
    vy
    copab
    mptfng.1
    vx
    vy
    cA
    cB
    df-mpt
    eqtri
    fnopabg
    bitri
end
