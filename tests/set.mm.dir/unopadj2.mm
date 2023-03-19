include "cuo.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cado.mm"
include "clo.mm"
include "unoplin.mm"
include "lnopf.mm"
include "syl.mm"
include "cnvunop.mm"
include "3syl.mm"
include "unopadj.mm"
include "3expib.mm"
include "ralrimivv.mm"
include "adjeq.mm"
include "syl3anc.mm"

theorem unopadj2
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( T e. UniOp -> ( adjh ` T ) = `' T )

  proof
    cT
    cuo
    wcel
    #
    chil
    chil
    cT
    wf
    #
    chil
    chil
    cT
    ccnv
    #
    wf
    #
    vx
    cv
    #
    cT
    cfv
    vy
    cv
    #
    csp
    co
    @4
    @5
    @2
    cfv
    csp
    co
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    cT
    cado
    cfv
    @2
    wceq
    @0
    cT
    clo
    wcel
    @1
    cT
    unoplin
    cT
    lnopf
    syl
    @0
    @2
    cuo
    wcel
    @2
    clo
    wcel
    @3
    cT
    cnvunop
    @2
    unoplin
    @2
    lnopf
    3syl
    @0
    @6
    vx
    vy
    chil
    chil
    @0
    @4
    chil
    wcel
    @5
    chil
    wcel
    @6
    @4
    @5
    cT
    unopadj
    3expib
    ralrimivv
    vx
    vy
    @2
    cT
    adjeq
    syl3anc
end
