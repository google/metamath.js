include "cfmtno.mm"
include "crn.mm"
include "cprime.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cmpt.mm"
include "wf1.mm"
include "cfn.mm"
include "wnel.mm"
include "eqid.mm"
include "prmdvdsfmtnof1.mm"
include "wi.mm"
include "ax-1.mm"
include "wn.mm"
include "wcel.mm"
include "nnel.mm"
include "wa.mm"
include "fmtnoinf.mm"
include "f1fi.mm"
include "df-nel.mm"
include "pm2.21.mm"
include "sylbi.mm"
include "mpsyl.mm"
include "ex.mm"
include "pm2.61i.mm"
include "ax-mp.mm"

theorem prminf2
  let vf: setvar f
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x


  assert |- Prime e/ Fin

  proof
    cfmtno
    crn
    #
    cprime
    vf
    @0
    vp
    cv
    vf
    cv
    cdvds
    wbr
    vp
    cprime
    crab
    cr
    clt
    cinf
    cmpt
    #
    wf1
    #
    cprime
    cfn
    wnel
    #
    vf
    @1
    vp
    @1
    eqid
    prmdvdsfmtnof1
    @3
    @2
    @3
    wi
    #
    @3
    @2
    ax-1
    @3
    wn
    cprime
    cfn
    wcel
    #
    @4
    cprime
    cfn
    nnel
    @5
    @2
    @3
    @0
    cfn
    wnel
    #
    @5
    @2
    wa
    @0
    cfn
    wcel
    #
    @3
    fmtnoinf
    @0
    cprime
    @1
    f1fi
    @6
    @7
    wn
    @7
    @3
    wi
    @0
    cfn
    df-nel
    @7
    @3
    pm2.21
    sylbi
    mpsyl
    ex
    sylbi
    pm2.61i
    ax-mp
end
