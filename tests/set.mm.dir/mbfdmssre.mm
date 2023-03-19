include "cmbf.mm"
include "wcel.mm"
include "cc.mm"
include "cr.mm"
include "cpm.mm"
include "co.mm"
include "cdm.mm"
include "wss.mm"
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
include "elpmi2.mm"
include "syl.mm"

theorem mbfdmssre
  let cF: class F
  let vx: setvar x
  let vk: setvar k


  assert |- ( F e. MblFn -> dom F C_ RR )

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
    cr
    wss
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
    @2
    cima
    @3
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
    cc
    cr
    cF
    elpmi2
    syl
end
