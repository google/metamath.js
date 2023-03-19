include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wbr.mm"
include "wn.mm"
include "eqid.mm"
include "wne.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "cvrne.mm"
include "syl31anc.mm"
include "ex.mm"
include "necon2bd.mm"
include "mpi.mm"

theorem cvrnrefN
  let cA: class A
  let cB: class B
  let cC: class C
  let cK: class K
  let cX: class X
  assume cvrne.b: |- B = ( Base ` K )
  assume cvrne.c: |- C = ( <o ` K )


  assert |- ( ( K e. A /\ X e. B ) -> -. X C X )

  proof
    cK
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cX
    wceq
    cX
    cX
    cC
    wbr
    #
    wn
    cX
    eqid
    @2
    @3
    cX
    cX
    @2
    @3
    cX
    cX
    wne
    #
    @2
    @3
    wa
    @0
    @1
    @1
    @3
    @4
    @0
    @1
    @3
    simpll
    @0
    @1
    @3
    simplr
    #
    @5
    @2
    @3
    simpr
    cA
    cB
    cC
    cK
    cX
    cX
    cvrne.b
    cvrne.c
    cvrne
    syl31anc
    ex
    necon2bd
    mpi
end
