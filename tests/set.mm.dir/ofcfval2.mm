include "wfn.mm"
include "cmpt.mm"
include "wcel.mm"
include "wral.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "fnmpt.mm"
include "syl.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "fvmpt2d.mm"
include "ofcfval.mm"

theorem ofcfval2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  assume ofcfval2.1: |- ( ph -> A e. V )
  assume ofcfval2.2: |- ( ph -> C e. W )
  assume ofcfval2.3: |- ( ( ph /\ x e. A ) -> B e. X )
  assume ofcfval2.4: |- ( ph -> F = ( x e. A |-> B ) )

  disjoint A x
  disjoint C x
  disjoint F x
  disjoint R x
  disjoint ph x
  assert |- ( ph -> ( F oFC R C ) = ( x e. A |-> ( B R C ) ) )

  proof
    wph
    vx
    cA
    cB
    cC
    cR
    cF
    cV
    cW
    wph
    cF
    cA
    wfn
    vx
    cA
    cB
    cmpt
    #
    cA
    wfn
    #
    wph
    cB
    cX
    wcel
    #
    vx
    cA
    wral
    @1
    wph
    @2
    vx
    cA
    ofcfval2.3
    ralrimiva
    vx
    cA
    cB
    @0
    cX
    @0
    eqid
    fnmpt
    syl
    wph
    cA
    cF
    @0
    ofcfval2.4
    fneq1d
    mpbird
    ofcfval2.1
    ofcfval2.2
    wph
    vx
    cA
    cB
    cF
    cX
    ofcfval2.4
    ofcfval2.3
    fvmpt2d
    ofcfval
end
