include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "elfvdm.mm"
include "cv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "c0.mm"
include "wceq.mm"
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
include "cab.mm"
include "cvv.mm"
include "vex.mm"
include "ovex.mm"
include "mapex.mm"
include "mp2an.mm"
include "simp1.mm"
include "ss2abi.mm"
include "ssexi.mm"
include "df-meas.mm"
include "dmmpti.mm"
include "syl6eleq.mm"

theorem measbase
  let cS: class S
  let cM: class M
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vs: setvar s


  assert |- ( M e. ( measures ` S ) -> S e. U. ran sigAlgebra )

  proof
    cM
    cS
    cmeas
    cfv
    wcel
    cS
    cmeas
    cdm
    csiga
    crn
    cuni
    #
    cM
    cS
    cmeas
    elfvdm
    vs
    @0
    vs
    cv
    #
    cc0
    cpnf
    cicc
    co
    #
    vm
    cv
    #
    wf
    #
    c0
    @3
    cfv
    cc0
    wceq
    #
    vx
    cv
    #
    com
    cdom
    wbr
    vy
    @6
    vy
    cv
    #
    wdisj
    wa
    @6
    cuni
    @3
    cfv
    @6
    @7
    @3
    cfv
    vy
    cesum
    wceq
    wi
    vx
    @1
    cpw
    wral
    #
    w3a
    #
    vm
    cab
    #
    cmeas
    @10
    @4
    vm
    cab
    #
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    @11
    cvv
    wcel
    vs
    vex
    cc0
    cpnf
    cicc
    ovex
    @1
    @2
    cvv
    cvv
    vm
    mapex
    mp2an
    @9
    @4
    vm
    @4
    @5
    @8
    simp1
    ss2abi
    ssexi
    vx
    vy
    vm
    vs
    df-meas
    dmmpti
    syl6eleq
end
