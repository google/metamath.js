include "cado.mm"
include "cdm.mm"
include "wf1o.mm"
include "wfn.mm"
include "ccnv.mm"
include "wfun.mm"
include "crn.mm"
include "wceq.mm"
include "funadj.mm"
include "funfn.mm"
include "mpbi.mm"
include "funcnvadj.mm"
include "df-rn.mm"
include "cnvadj.mm"
include "dmeqi.mm"
include "eqtri.mm"
include "dff1o2.mm"
include "mpbir3an.mm"

theorem adj1o
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cT: class T


  assert |- adjh : dom adjh -1-1-onto-> dom adjh

  proof
    cado
    cdm
    #
    @0
    cado
    wf1o
    cado
    @0
    wfn
    #
    cado
    ccnv
    #
    wfun
    cado
    crn
    #
    @0
    wceq
    cado
    wfun
    @1
    funadj
    cado
    funfn
    mpbi
    funcnvadj
    @3
    @2
    cdm
    @0
    cado
    df-rn
    @2
    cado
    cnvadj
    dmeqi
    eqtri
    @0
    @0
    cado
    dff1o2
    mpbir3an
end
