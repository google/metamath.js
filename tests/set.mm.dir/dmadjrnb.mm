include "cado.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "dmadjrn.mm"
include "wn.mm"
include "c0.mm"
include "chil.mm"
include "wf.mm"
include "wceq.mm"
include "c0v.mm"
include "ax-hv0cl.mm"
include "n0ii.mm"
include "eqcom.mm"
include "mtbir.mm"
include "dm0.mm"
include "eqeq1i.mm"
include "fdm.mm"
include "mto.mm"
include "dmadjop.mm"
include "ndmfv.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "con4i.mm"
include "impbii.mm"

theorem dmadjrnb
  let cT: class T


  assert |- ( T e. dom adjh <-> ( adjh ` T ) e. dom adjh )

  proof
    cT
    cado
    cdm
    #
    wcel
    #
    cT
    cado
    cfv
    #
    @0
    wcel
    #
    cT
    dmadjrn
    @1
    @3
    @1
    wn
    #
    @3
    c0
    @0
    wcel
    #
    @5
    chil
    chil
    c0
    wf
    #
    @6
    c0
    cdm
    #
    chil
    wceq
    #
    @8
    c0
    chil
    wceq
    #
    @9
    chil
    c0
    wceq
    c0v
    chil
    ax-hv0cl
    n0ii
    c0
    chil
    eqcom
    mtbir
    @7
    c0
    chil
    dm0
    eqeq1i
    mtbir
    chil
    chil
    c0
    fdm
    mto
    c0
    dmadjop
    mto
    @4
    @2
    c0
    @0
    cT
    cado
    ndmfv
    eleq1d
    mtbiri
    con4i
    impbii
end
