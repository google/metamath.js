include "cort.mm"
include "cfv.mm"
include "wcel.mm"
include "cpjh.mm"
include "c0v.mm"
include "wceq.mm"
include "choccli.mm"
include "pjoc1i.mm"
include "pjococi.mm"
include "fveq2i.mm"
include "fveq1i.mm"
include "eqeq1i.mm"
include "bitri.mm"

theorem pjoc2i
  let cA: class A
  let cH: class H
  assume pjoc2.1: |- H e. CH
  assume pjoc2.2: |- A e. ~H


  assert |- ( A e. ( _|_ ` H ) <-> ( ( projh ` H ) ` A ) = 0h )

  proof
    cA
    cH
    cort
    cfv
    #
    wcel
    cA
    @0
    cort
    cfv
    #
    cpjh
    cfv
    #
    cfv
    #
    c0v
    wceq
    cA
    cH
    cpjh
    cfv
    #
    cfv
    #
    c0v
    wceq
    cA
    @0
    cH
    pjoc2.1
    choccli
    pjoc2.2
    pjoc1i
    @3
    @5
    c0v
    cA
    @2
    @4
    @1
    cH
    cpjh
    cH
    pjoc2.1
    pjococi
    fveq2i
    fveq1i
    eqeq1i
    bitri
end
