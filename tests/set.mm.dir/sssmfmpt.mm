include "cmpt.mm"
include "cres.mm"
include "csmblfn.mm"
include "cfv.mm"
include "resmptd.mm"
include "eqcomd.mm"
include "sssmf.mm"
include "eqeltrd.mm"

theorem sssmfmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let vk: setvar k
  assume sssmfmpt.s: |- ( ph -> S e. SAlg )
  assume sssmfmpt.f: |- ( ph -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume sssmfmpt.c: |- ( ph -> C C_ A )

  disjoint A x
  disjoint C x
  disjoint k x
  assert |- ( ph -> ( x e. C |-> B ) e. ( SMblFn ` S ) )

  proof
    wph
    vx
    cC
    cB
    cmpt
    #
    vx
    cA
    cB
    cmpt
    #
    cC
    cres
    #
    cS
    csmblfn
    cfv
    wph
    @2
    @0
    wph
    vx
    cA
    cC
    cB
    sssmfmpt.c
    resmptd
    eqcomd
    wph
    cC
    cS
    @1
    sssmfmpt.s
    sssmfmpt.f
    sssmf
    eqeltrd
end
