include "c0.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wceq.mm"
include "eqid.mm"
include "fn0.mm"
include "mpbir.mm"
include "rn0.mm"
include "0ss.mm"
include "eqsstri.mm"
include "df-f.mm"
include "mpbir2an.mm"

theorem f0
  let cA: class A


  assert |- (/) : (/) --> A

  proof
    c0
    cA
    c0
    wf
    c0
    c0
    wfn
    #
    c0
    crn
    #
    cA
    wss
    @0
    c0
    c0
    wceq
    c0
    eqid
    c0
    fn0
    mpbir
    @1
    c0
    cA
    rn0
    cA
    0ss
    eqsstri
    c0
    cA
    c0
    df-f
    mpbir2an
end
