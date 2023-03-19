include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "cuni.mm"
include "wceq.mm"
include "cdif.mm"
include "cfn.mm"
include "wrex.mm"
include "w3a.mm"
include "cixp.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cpt.mm"
include "ctg.mm"
include "ctb.mm"
include "wss.mm"
include "ctop.mm"
include "wf.mm"
include "eqid.mm"
include "ptbas.mm"
include "syl2anc.mm"
include "bastg.mm"
include "syl.mm"
include "ffn.mm"
include "ptval.mm"
include "sseqtr4d.mm"
include "elptr2.mm"
include "sseldd.mm"

theorem ptopn
  let wph: wff ph
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cV: class V
  let cW: class W
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ptopn.1: |- ( ph -> A e. V )
  assume ptopn.2: |- ( ph -> F : A --> Top )
  assume ptopn.3: |- ( ph -> W e. Fin )
  assume ptopn.4: |- ( ( ph /\ k e. A ) -> S e. ( F ` k ) )
  assume ptopn.5: |- ( ( ph /\ k e. ( A \ W ) ) -> S = U. ( F ` k ) )

  disjoint A k
  disjoint F k
  disjoint V k
  disjoint k ph
  disjoint W k
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint S g
  disjoint S x
  disjoint S y
  disjoint V g
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint W y
  assert |- ( ph -> X_ k e. A S e. ( Xt_ ` F ) )

  proof
    wph
    vg
    cv
    #
    cA
    wfn
    vy
    cv
    #
    @0
    cfv
    #
    @1
    cF
    cfv
    #
    wcel
    vy
    cA
    wral
    @2
    @3
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
    vx
    cv
    vy
    cA
    @2
    cixp
    wceq
    wa
    vg
    wex
    vx
    cab
    #
    cF
    cpt
    cfv
    #
    vk
    cA
    cS
    cixp
    wph
    @4
    @4
    ctg
    cfv
    #
    @5
    wph
    @4
    ctb
    wcel
    #
    @4
    @6
    wss
    wph
    cA
    cV
    wcel
    #
    cA
    ctop
    cF
    wf
    #
    @7
    ptopn.1
    ptopn.2
    vx
    vy
    vz
    cA
    @4
    vg
    cF
    cV
    @4
    eqid
    #
    ptbas
    syl2anc
    @4
    ctb
    bastg
    syl
    wph
    @8
    cF
    cA
    wfn
    #
    @5
    @6
    wceq
    ptopn.1
    wph
    @9
    @11
    ptopn.2
    cA
    ctop
    cF
    ffn
    syl
    vx
    vy
    vz
    cA
    @4
    vg
    cF
    cV
    @10
    ptval
    syl2anc
    sseqtr4d
    wph
    vx
    vy
    vz
    cA
    @4
    cS
    vg
    vk
    cF
    cV
    cW
    @10
    ptopn.1
    ptopn.3
    ptopn.4
    ptopn.5
    elptr2
    sseldd
end
