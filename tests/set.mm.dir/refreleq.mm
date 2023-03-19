include "wceq.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "wrel.mm"
include "wa.mm"
include "wrefrel.mm"
include "dmeq.mm"
include "rneq.mm"
include "xpeq12d.mm"
include "ineq2d.mm"
include "id.mm"
include "sseq12d.mm"
include "releq.mm"
include "anbi12d.mm"
include "dfrefrel2.mm"
include "3bitr4g.mm"

theorem refreleq
  let cR: class R
  let cS: class S


  assert |- ( R = S -> ( RefRel R <-> RefRel S ) )

  proof
    cR
    cS
    wceq
    #
    cid
    cR
    cdm
    #
    cR
    crn
    #
    cxp
    #
    cin
    #
    cR
    wss
    #
    cR
    wrel
    #
    wa
    cid
    cS
    cdm
    #
    cS
    crn
    #
    cxp
    #
    cin
    #
    cS
    wss
    #
    cS
    wrel
    #
    wa
    cR
    wrefrel
    cS
    wrefrel
    @0
    @5
    @11
    @6
    @12
    @0
    @4
    @10
    cR
    cS
    @0
    @3
    @9
    cid
    @0
    @1
    @7
    @2
    @8
    cR
    cS
    dmeq
    cR
    cS
    rneq
    xpeq12d
    ineq2d
    @0
    id
    sseq12d
    cR
    cS
    releq
    anbi12d
    cR
    dfrefrel2
    cS
    dfrefrel2
    3bitr4g
end
