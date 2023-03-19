include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "pclssidN.mm"
include "eqimss.mm"
include "sylan9ss.mm"
include "ss0.mm"
include "syl.mm"
include "fveq2.mm"
include "pcl0N.mm"
include "sylan9eqr.mm"
include "adantlr.mm"
include "impbida.mm"

theorem pcl0bN
  let cA: class A
  let cP: class P
  let cU: class U
  let cK: class K
  assume pcl0b.a: |- A = ( Atoms ` K )
  assume pcl0b.c: |- U = ( PCl ` K )


  assert |- ( ( K e. HL /\ P C_ A ) -> ( ( U ` P ) = (/) <-> P = (/) ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wss
    #
    wa
    #
    cP
    cU
    cfv
    #
    c0
    wceq
    #
    cP
    c0
    wceq
    #
    @2
    @4
    wa
    cP
    c0
    wss
    @5
    @2
    @4
    cP
    @3
    c0
    cA
    cU
    cK
    chlt
    cP
    pcl0b.a
    pcl0b.c
    pclssidN
    @3
    c0
    eqimss
    sylan9ss
    cP
    ss0
    syl
    @0
    @5
    @4
    @1
    @5
    @0
    @3
    c0
    cU
    cfv
    c0
    cP
    c0
    cU
    fveq2
    cU
    cK
    pcl0b.c
    pcl0N
    sylan9eqr
    adantlr
    impbida
end
