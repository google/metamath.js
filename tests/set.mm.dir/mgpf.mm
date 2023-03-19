include "crg.mm"
include "cmnd.mm"
include "cmgp.mm"
include "cres.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "cvv.mm"
include "wss.mm"
include "fnmgp.mm"
include "ssv.mm"
include "fnssres.mm"
include "mp2an.mm"
include "fvres.mm"
include "eqid.mm"
include "ringmgp.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"

theorem mgpf
  let va: setvar a


  assert |- ( mulGrp |` Ring ) : Ring --> Mnd

  proof
    crg
    cmnd
    cmgp
    crg
    cres
    #
    wf
    @0
    crg
    wfn
    #
    va
    cv
    #
    @0
    cfv
    #
    cmnd
    wcel
    #
    va
    crg
    wral
    cmgp
    cvv
    wfn
    crg
    cvv
    wss
    @1
    fnmgp
    crg
    ssv
    cvv
    crg
    cmgp
    fnssres
    mp2an
    @4
    va
    crg
    @2
    crg
    wcel
    @3
    @2
    cmgp
    cfv
    #
    cmnd
    @2
    crg
    cmgp
    fvres
    @2
    @5
    @5
    eqid
    ringmgp
    eqeltrd
    rgen
    va
    crg
    cmnd
    @0
    ffnfv
    mpbir2an
end
