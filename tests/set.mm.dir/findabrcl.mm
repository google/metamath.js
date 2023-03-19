include "com.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "crdg.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "fveq2.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "syl.mm"
include "adantr.mm"
include "findreccl.mm"
include "imp.mm"
include "eqeltrd.mm"

theorem findabrcl
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cP: class P
  let cG: class G
  assume findabrcl.1: |- ( z e. P -> ( G ` z ) e. P )

  disjoint G x
  disjoint A x
  disjoint C x
  disjoint G z
  disjoint A z
  disjoint P z
  assert |- ( ( C e. _om /\ A e. P ) -> ( ( x e. _V |-> ( rec ( G , A ) ` x ) ) ` C ) e. P )

  proof
    cC
    com
    wcel
    #
    cA
    cP
    wcel
    #
    wa
    cC
    vx
    cvv
    vx
    cv
    #
    cG
    cA
    crdg
    #
    cfv
    #
    cmpt
    #
    cfv
    #
    cC
    @3
    cfv
    #
    cP
    @0
    @6
    @7
    wceq
    #
    @1
    @0
    cC
    cvv
    wcel
    @8
    cC
    com
    elex
    vx
    cC
    @4
    @7
    cvv
    @5
    @2
    cC
    @3
    fveq2
    @5
    eqid
    cC
    @3
    fvex
    fvmpt
    syl
    adantr
    @0
    @1
    @7
    cP
    wcel
    vz
    cA
    cC
    cP
    cG
    findabrcl.1
    findreccl
    imp
    eqeltrd
end
