include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
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
include "cuni.mm"
include "cesum.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "w3a.mm"
include "csiga.mm"
include "crn.mm"
include "wb.mm"
include "measbase.mm"
include "ismeas.mm"
include "syl.mm"
include "ibi.mm"
include "simp2d.mm"

theorem measvnul
  let cS: class S
  let cM: class M
  let vx: setvar x
  let vy: setvar y


  assert |- ( M e. ( measures ` S ) -> ( M ` (/) ) = 0 )

  proof
    cM
    cS
    cmeas
    cfv
    wcel
    #
    cS
    cc0
    cpnf
    cicc
    co
    cM
    wf
    #
    c0
    cM
    cfv
    cc0
    wceq
    #
    vy
    cv
    #
    com
    cdom
    wbr
    vx
    @3
    vx
    cv
    #
    wdisj
    wa
    @3
    cuni
    cM
    cfv
    @3
    @4
    cM
    cfv
    vx
    cesum
    wceq
    wi
    vy
    cS
    cpw
    wral
    #
    @0
    @1
    @2
    @5
    w3a
    #
    @0
    cS
    csiga
    crn
    cuni
    wcel
    @0
    @6
    wb
    cS
    cM
    measbase
    vy
    vx
    cS
    cM
    ismeas
    syl
    ibi
    simp2d
end
