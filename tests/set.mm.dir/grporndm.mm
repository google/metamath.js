include "cgr.mm"
include "wcel.mm"
include "crn.mm"
include "cxp.mm"
include "wfo.mm"
include "cdm.mm"
include "wceq.mm"
include "eqid.mm"
include "grpofo.mm"
include "wf.mm"
include "fof.mm"
include "fdm.mm"
include "syl.mm"
include "dmeqd.mm"
include "dmxpid.mm"
include "syl6req.mm"

theorem grporndm
  let cG: class G


  assert |- ( G e. GrpOp -> ran G = dom dom G )

  proof
    cG
    cgr
    wcel
    cG
    crn
    #
    @0
    cxp
    #
    @0
    cG
    wfo
    #
    @0
    cG
    cdm
    #
    cdm
    #
    wceq
    cG
    @0
    @0
    eqid
    grpofo
    @2
    @4
    @1
    cdm
    @0
    @2
    @3
    @1
    @2
    @1
    @0
    cG
    wf
    @3
    @1
    wceq
    @1
    @0
    cG
    fof
    @1
    @0
    cG
    fdm
    syl
    dmeqd
    @0
    dmxpid
    syl6req
    syl
end
