include "wcel.mm"
include "ctop.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "cuni.mm"
include "wceq.mm"
include "cdif.mm"
include "cfn.mm"
include "wrex.mm"
include "w3a.mm"
include "cixp.mm"
include "wex.mm"
include "cab.mm"
include "ctg.mm"
include "ctb.mm"
include "eqid.mm"
include "ptbas.mm"
include "unitg.mm"
include "syl.mm"
include "cpt.mm"
include "ffn.mm"
include "ptval.mm"
include "sylan2.mm"
include "syl5eq.mm"
include "unieqd.mm"
include "ptuni2.mm"
include "3eqtr4rd.mm"

theorem ptuni
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cJ: class J
  let cV: class V
  let vg: setvar g
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  assume ptuni.1: |- J = ( Xt_ ` F )

  disjoint A x
  disjoint F x
  disjoint V x
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F g
  disjoint F k
  disjoint F y
  disjoint F z
  disjoint V g
  disjoint V k
  disjoint V y
  disjoint V z
  assert |- ( ( A e. V /\ F : A --> Top ) -> X_ x e. A U. ( F ` x ) = U. J )

  proof
    cA
    cV
    wcel
    #
    cA
    ctop
    cF
    wf
    #
    wa
    #
    vg
    cv
    #
    cA
    wfn
    vy
    cv
    #
    @3
    cfv
    #
    @4
    cF
    cfv
    #
    wcel
    vy
    cA
    wral
    @5
    @6
    cuni
    wceq
    vy
    cA
    vz
    cv
    cdif
    wral
    vz
    cfn
    wrex
    w3a
    vk
    cv
    vy
    cA
    @5
    cixp
    wceq
    wa
    vg
    wex
    vk
    cab
    #
    ctg
    cfv
    #
    cuni
    #
    @7
    cuni
    #
    cJ
    cuni
    vx
    cA
    vx
    cv
    cF
    cfv
    cuni
    cixp
    @2
    @7
    ctb
    wcel
    @9
    @10
    wceq
    vk
    vy
    vz
    cA
    @7
    vg
    cF
    cV
    @7
    eqid
    #
    ptbas
    @7
    ctb
    unitg
    syl
    @2
    cJ
    @8
    @2
    cJ
    cF
    cpt
    cfv
    #
    @8
    ptuni.1
    @1
    @0
    cF
    cA
    wfn
    @12
    @8
    wceq
    cA
    ctop
    cF
    ffn
    vk
    vy
    vz
    cA
    @7
    vg
    cF
    cV
    @11
    ptval
    sylan2
    syl5eq
    unieqd
    vk
    vy
    vz
    cA
    @7
    vg
    vx
    cF
    cV
    @11
    ptuni2
    3eqtr4rd
end
