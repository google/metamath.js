include "cmpt.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "eqid.mm"
include "fmptdf.mm"
include "sge0repnf.mm"

theorem sge0repnfmpt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cV: class V
  let vx: setvar x
  assume sge0repnfmpt.k: |- F/ k ph
  assume sge0repnfmpt.a: |- ( ph -> A e. V )
  assume sge0repnfmpt.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )

  disjoint A k
  disjoint k x
  assert |- ( ph -> ( ( sum^ ` ( k e. A |-> B ) ) e. RR <-> -. ( sum^ ` ( k e. A |-> B ) ) = +oo ) )

  proof
    wph
    vk
    cA
    cB
    cmpt
    #
    cV
    cA
    sge0repnfmpt.a
    wph
    vk
    cA
    cB
    cc0
    cpnf
    cicc
    co
    @0
    sge0repnfmpt.k
    sge0repnfmpt.b
    @0
    eqid
    fmptdf
    sge0repnf
end
