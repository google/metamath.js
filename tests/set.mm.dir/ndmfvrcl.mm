include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "wn.mm"
include "c0.mm"
include "ndmfv.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "con4i.mm"
include "syl6eleq.mm"

theorem ndmfvrcl
  let cA: class A
  let cS: class S
  let cF: class F
  assume ndmfvrcl.1: |- dom F = S
  assume ndmfvrcl.2: |- -. (/) e. S


  assert |- ( ( F ` A ) e. S -> A e. S )

  proof
    cA
    cF
    cfv
    #
    cS
    wcel
    #
    cA
    cF
    cdm
    #
    cS
    cA
    @2
    wcel
    #
    @1
    @3
    wn
    #
    @1
    c0
    cS
    wcel
    ndmfvrcl.2
    @4
    @0
    c0
    cS
    cA
    cF
    ndmfv
    eleq1d
    mtbiri
    con4i
    ndmfvrcl.1
    syl6eleq
end
