include "cmeas.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cdm.mm"
include "csiga.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "c0.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "cesum.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "w3a.mm"
include "isrnmeas.mm"
include "simpld.mm"

theorem dmmeas
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vs: setvar s


  assert |- ( M e. U. ran measures -> dom M e. U. ran sigAlgebra )

  proof
    cM
    cmeas
    crn
    cuni
    wcel
    cM
    cdm
    #
    csiga
    crn
    cuni
    wcel
    @0
    cc0
    cpnf
    cicc
    co
    cM
    wf
    c0
    cM
    cfv
    cc0
    wceq
    vx
    cv
    #
    com
    cdom
    wbr
    vy
    @1
    vy
    cv
    #
    wdisj
    wa
    @1
    cuni
    cM
    cfv
    @1
    @2
    cM
    cfv
    vy
    cesum
    wceq
    wi
    vx
    @0
    cpw
    wral
    w3a
    vx
    vy
    cM
    isrnmeas
    simpld
end
