include "come.mm"
include "wcel.mm"
include "cdm.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cuni.mm"
include "cpw.mm"
include "wceq.mm"
include "c0.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "cres.mm"
include "csumge0.mm"
include "wi.mm"
include "isome.mm"
include "ibi.mm"
include "simplld.mm"
include "simplrd.mm"

theorem omedm
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( O e. OutMeas -> dom O = ~P U. dom O )

  proof
    cO
    come
    wcel
    #
    cO
    cdm
    #
    cc0
    cpnf
    cicc
    co
    cO
    wf
    #
    @1
    @1
    cuni
    cpw
    #
    wceq
    #
    c0
    cO
    cfv
    cc0
    wceq
    #
    @0
    @2
    @4
    wa
    @5
    wa
    #
    vy
    cv
    cO
    cfv
    vx
    cv
    #
    cO
    cfv
    cle
    wbr
    vy
    @7
    cpw
    wral
    vx
    @3
    wral
    #
    @7
    com
    cdom
    wbr
    @7
    cuni
    cO
    cfv
    cO
    @7
    cres
    csumge0
    cfv
    cle
    wbr
    wi
    vx
    @1
    cpw
    wral
    #
    @0
    @6
    @8
    wa
    @9
    wa
    vx
    vy
    cO
    come
    isome
    ibi
    simplld
    simplrd
end
