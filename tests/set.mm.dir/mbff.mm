include "cmbf.mm"
include "wcel.mm"
include "cc.mm"
include "cr.mm"
include "cpm.mm"
include "co.mm"
include "cdm.mm"
include "wf.mm"
include "cre.mm"
include "ccom.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cvol.mm"
include "cim.mm"
include "wa.mm"
include "cioo.mm"
include "crn.mm"
include "wral.mm"
include "ismbf1.mm"
include "simplbi.mm"
include "wss.mm"
include "cnex.mm"
include "reex.mm"
include "elpm2.mm"
include "syl.mm"

theorem mbff
  let cF: class F
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( F e. MblFn -> F : dom F --> CC )

  proof
    cF
    cmbf
    wcel
    #
    cF
    cc
    cr
    cpm
    co
    wcel
    #
    cF
    cdm
    #
    cc
    cF
    wf
    #
    @0
    @1
    cre
    cF
    ccom
    ccnv
    vx
    cv
    #
    cima
    cvol
    cdm
    #
    wcel
    cim
    cF
    ccom
    ccnv
    @4
    cima
    @5
    wcel
    wa
    vx
    cioo
    crn
    wral
    vx
    cF
    ismbf1
    simplbi
    @1
    @3
    @2
    cr
    wss
    cc
    cr
    cF
    cnex
    reex
    elpm2
    simplbi
    syl
end
