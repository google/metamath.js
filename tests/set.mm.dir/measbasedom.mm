include "cmeas.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "c0.mm"
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
include "csiga.mm"
include "isrnmeas.mm"
include "simprd.mm"
include "wb.mm"
include "dmmeas.mm"
include "ismeas.mm"
include "syl.mm"
include "mpbird.mm"
include "wfun.mm"
include "cab.mm"
include "df-meas.mm"
include "funmpt2.mm"
include "elunirn2.mm"
include "mpan.mm"
include "impbii.mm"

theorem measbasedom
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vs: setvar s


  assert |- ( M e. U. ran measures <-> M e. ( measures ` dom M ) )

  proof
    cM
    cmeas
    crn
    cuni
    wcel
    #
    cM
    cM
    cdm
    #
    cmeas
    cfv
    wcel
    #
    @0
    @2
    @1
    cc0
    cpnf
    cicc
    co
    #
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
    @4
    vy
    cv
    #
    wdisj
    wa
    #
    @4
    cuni
    #
    cM
    cfv
    @4
    @5
    cM
    cfv
    vy
    cesum
    wceq
    wi
    vx
    @1
    cpw
    wral
    w3a
    #
    @0
    @1
    csiga
    crn
    cuni
    #
    wcel
    #
    @8
    vx
    vy
    cM
    isrnmeas
    simprd
    @0
    @10
    @2
    @8
    wb
    cM
    dmmeas
    vx
    vy
    @1
    cM
    ismeas
    syl
    mpbird
    cmeas
    wfun
    @2
    @0
    vs
    @9
    vs
    cv
    #
    @3
    vm
    cv
    #
    wf
    c0
    @12
    cfv
    cc0
    wceq
    @6
    @7
    @12
    cfv
    @4
    @5
    @12
    cfv
    vy
    cesum
    wceq
    wi
    vx
    @11
    cpw
    wral
    w3a
    vm
    cab
    cmeas
    vx
    vy
    vm
    vs
    df-meas
    funmpt2
    @1
    cM
    cmeas
    elunirn2
    mpan
    impbii
end
