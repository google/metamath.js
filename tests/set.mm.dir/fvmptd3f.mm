include "cv.mm"
include "wceq.mm"
include "cmpt.mm"
include "wi.mm"
include "nfmpt1.mm"
include "nfeq.mm"
include "nfim.mm"
include "cvv.mm"
include "wcel.mm"
include "wex.mm"
include "elexd.mm"
include "isset.mm"
include "sylib.mm"
include "cfv.mm"
include "wa.mm"
include "fveq1.mm"
include "simpr.mm"
include "fveq2d.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "eqeq2d.mm"
include "sylbid.mm"
include "syl5.mm"
include "exlimdd.mm"

theorem fvmptd3f
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cF: class F
  let cV: class V
  assume fvmptdf.1: |- ( ph -> A e. D )
  assume fvmptdf.2: |- ( ( ph /\ x = A ) -> B e. V )
  assume fvmptdf.3: |- ( ( ph /\ x = A ) -> ( ( F ` A ) = B -> ps ) )
  assume fvmptd3f.4: |- F/_ x F
  assume fvmptd3f.5: |- F/ x ps
  assume fvmptd3f.6: |- F/ x ph

  disjoint A x
  disjoint D x
  assert |- ( ph -> ( F = ( x e. D |-> B ) -> ps ) )

  proof
    wph
    vx
    cv
    #
    cA
    wceq
    #
    cF
    vx
    cD
    cB
    cmpt
    #
    wceq
    #
    wps
    wi
    vx
    fvmptd3f.6
    @3
    wps
    vx
    vx
    cF
    @2
    fvmptd3f.4
    vx
    cD
    cB
    nfmpt1
    nfeq
    fvmptd3f.5
    nfim
    wph
    cA
    cvv
    wcel
    @1
    vx
    wex
    wph
    cA
    cD
    fvmptdf.1
    elexd
    vx
    cA
    isset
    sylib
    @3
    cA
    cF
    cfv
    #
    cA
    @2
    cfv
    #
    wceq
    #
    wph
    @1
    wa
    #
    wps
    cA
    cF
    @2
    fveq1
    @7
    @6
    @4
    cB
    wceq
    wps
    @7
    @5
    cB
    @4
    @7
    @0
    @2
    cfv
    #
    @5
    cB
    @7
    @0
    cA
    @2
    wph
    @1
    simpr
    #
    fveq2d
    @7
    @0
    cD
    wcel
    cB
    cV
    wcel
    @8
    cB
    wceq
    @7
    @0
    cA
    cD
    @9
    wph
    cA
    cD
    wcel
    @1
    fvmptdf.1
    adantr
    eqeltrd
    fvmptdf.2
    vx
    cD
    cB
    cV
    @2
    @2
    eqid
    fvmpt2
    syl2anc
    eqtr3d
    eqeq2d
    fvmptdf.3
    sylbid
    syl5
    exlimdd
end
