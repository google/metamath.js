include "cr.mm"
include "cmpt.mm"
include "wf.mm"
include "cdm.mm"
include "eqid.mm"
include "smff.mm"
include "dmmptdf.mm"
include "eqcomd.mm"
include "feq2d.mm"
include "mpbird.mm"

theorem smffmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cV: class V
  let vk: setvar k
  assume smffmpt.x: |- F/ x ph
  assume smffmpt.s: |- ( ph -> S e. SAlg )
  assume smffmpt.b: |- ( ( ph /\ x e. A ) -> B e. V )
  assume smffmpt.m: |- ( ph -> ( x e. A |-> B ) e. ( SMblFn ` S ) )

  disjoint A x
  disjoint k x
  assert |- ( ph -> ( x e. A |-> B ) : A --> RR )

  proof
    wph
    cA
    cr
    vx
    cA
    cB
    cmpt
    #
    wf
    @0
    cdm
    #
    cr
    @0
    wf
    wph
    @1
    cS
    @0
    smffmpt.s
    smffmpt.m
    @1
    eqid
    smff
    wph
    cA
    @1
    cr
    @0
    wph
    @1
    cA
    wph
    vx
    @0
    cA
    cB
    cV
    smffmpt.x
    @0
    eqid
    smffmpt.b
    dmmptdf
    eqcomd
    feq2d
    mpbird
end
