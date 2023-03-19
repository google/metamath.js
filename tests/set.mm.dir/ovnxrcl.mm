include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cxr.mm"
include "covoln.mm"
include "cfv.mm"
include "iccssxr.mm"
include "ovncl.mm"
include "sseldi.mm"

theorem ovnxrcl
  let wph: wff ph
  let cA: class A
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume ovnxrcl.1: |- ( ph -> X e. Fin )
  assume ovnxrcl.2: |- ( ph -> A C_ ( RR ^m X ) )


  assert |- ( ph -> ( ( voln* ` X ) ` A ) e. RR* )

  proof
    wph
    cc0
    cpnf
    cicc
    co
    cxr
    cA
    cX
    covoln
    cfv
    cfv
    cc0
    cpnf
    iccssxr
    wph
    cA
    cX
    ovnxrcl.1
    ovnxrcl.2
    ovncl
    sseldi
end
