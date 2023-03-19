include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cxr.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "iccssxr.mm"
include "sge0clmpt.mm"
include "sseldi.mm"

theorem sge0xrclmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vk: setvar k
  assume sge0xrclmpt.xph: |- F/ x ph
  assume sge0xrclmpt.a: |- ( ph -> A e. V )
  assume sge0xrclmpt.b: |- ( ( ph /\ x e. A ) -> B e. ( 0 [,] +oo ) )

  disjoint A x
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( x e. A |-> B ) ) e. RR* )

  proof
    wph
    cc0
    cpnf
    cicc
    co
    cxr
    vx
    cA
    cB
    cmpt
    csumge0
    cfv
    cc0
    cpnf
    iccssxr
    wph
    vx
    cA
    cB
    cV
    sge0xrclmpt.xph
    sge0xrclmpt.a
    sge0xrclmpt.b
    sge0clmpt
    sseldi
end
