include "cmpt.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "eqid.mm"
include "fmptdf.mm"
include "sge0cl.mm"

theorem sge0clmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vk: setvar k
  assume sge0clmpt.xph: |- F/ x ph
  assume sge0clmpt.a: |- ( ph -> A e. V )
  assume sge0clmpt.b: |- ( ( ph /\ x e. A ) -> B e. ( 0 [,] +oo ) )

  disjoint A x
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( x e. A |-> B ) ) e. ( 0 [,] +oo ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    cV
    cA
    sge0clmpt.a
    wph
    vx
    cA
    cB
    cc0
    cpnf
    cicc
    co
    @0
    sge0clmpt.xph
    sge0clmpt.b
    @0
    eqid
    fmptdf
    sge0cl
end
