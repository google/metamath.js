include "cnq.mm"
include "cxp.mm"
include "cplq.mm"
include "wf.mm"
include "cerq.mm"
include "cplpq.mm"
include "ccom.mm"
include "cres.mm"
include "cnpi.mm"
include "wss.mm"
include "nqerf.mm"
include "addpqf.mm"
include "fco.mm"
include "mp2an.mm"
include "cv.mm"
include "elpqn.mm"
include "ssriv.mm"
include "xpss12.mm"
include "fssres.mm"
include "df-plq.mm"
include "feq1i.mm"
include "mpbir.mm"

theorem addnqf
  let vx: setvar x


  assert |- +Q : ( Q. X. Q. ) --> Q.

  proof
    cnq
    cnq
    cxp
    #
    cnq
    cplq
    wf
    @0
    cnq
    cerq
    cplpq
    ccom
    #
    @0
    cres
    #
    wf
    #
    cnpi
    cnpi
    cxp
    #
    @4
    cxp
    #
    cnq
    @1
    wf
    #
    @0
    @5
    wss
    #
    @3
    @4
    cnq
    cerq
    wf
    @5
    @4
    cplpq
    wf
    @6
    nqerf
    addpqf
    @5
    @4
    cnq
    cerq
    cplpq
    fco
    mp2an
    cnq
    @4
    wss
    #
    @8
    @7
    vx
    cnq
    @4
    vx
    cv
    elpqn
    ssriv
    #
    @9
    cnq
    @4
    cnq
    @4
    xpss12
    mp2an
    @5
    cnq
    @0
    @1
    fssres
    mp2an
    @0
    cnq
    cplq
    @2
    df-plq
    feq1i
    mpbir
end
