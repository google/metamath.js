include "c0.mm"
include "wne.mm"
include "cxp.mm"
include "c2nd.mm"
include "cres.mm"
include "wf.mm"
include "crn.mm"
include "wceq.mm"
include "wa.mm"
include "wfo.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wi.mm"
include "n0.mm"
include "cop.mm"
include "opelxp.mm"
include "cfv.mm"
include "fvres.mm"
include "vex.mm"
include "op2nd.mm"
include "syl6req.mm"
include "wfn.mm"
include "f2ndres.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnfvelrn.mm"
include "mpan.mm"
include "eqeltrd.mm"
include "sylbir.mm"
include "ex.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "ssrdv.mm"
include "frn.mm"
include "jctil.mm"
include "eqss.mm"
include "sylibr.mm"
include "dffo2.mm"

theorem fo2ndres
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A =/= (/) -> ( 2nd |` ( A X. B ) ) : ( A X. B ) -onto-> B )

  proof
    cA
    c0
    wne
    #
    cA
    cB
    cxp
    #
    cB
    c2nd
    @1
    cres
    #
    wf
    #
    @2
    crn
    #
    cB
    wceq
    #
    wa
    @1
    cB
    @2
    wfo
    @0
    @5
    @3
    @0
    @4
    cB
    wss
    #
    cB
    @4
    wss
    #
    wa
    @5
    @0
    @7
    @6
    @0
    vy
    cB
    @4
    @0
    vx
    cv
    #
    cA
    wcel
    #
    vx
    wex
    vy
    cv
    #
    cB
    wcel
    #
    @10
    @4
    wcel
    #
    wi
    #
    vx
    cA
    n0
    @9
    @13
    vx
    @9
    @11
    @12
    @9
    @11
    wa
    @8
    @10
    cop
    #
    @1
    wcel
    #
    @12
    @8
    @10
    cA
    cB
    opelxp
    @15
    @10
    @14
    @2
    cfv
    #
    @4
    @15
    @16
    @14
    c2nd
    cfv
    @10
    @14
    @1
    c2nd
    fvres
    @8
    @10
    vx
    vex
    vy
    vex
    op2nd
    syl6req
    @2
    @1
    wfn
    #
    @15
    @16
    @4
    wcel
    @3
    @17
    cA
    cB
    f2ndres
    #
    @1
    cB
    @2
    ffn
    ax-mp
    @1
    @14
    @2
    fnfvelrn
    mpan
    eqeltrd
    sylbir
    ex
    exlimiv
    sylbi
    ssrdv
    @3
    @6
    @18
    @1
    cB
    @2
    frn
    ax-mp
    jctil
    @4
    cB
    eqss
    sylibr
    @18
    jctil
    @1
    cB
    @2
    dffo2
    sylibr
end
