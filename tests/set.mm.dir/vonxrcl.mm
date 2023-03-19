include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cxr.mm"
include "cvoln.mm"
include "cfv.mm"
include "iccssxr.mm"
include "voncl.mm"
include "sseldi.mm"

theorem vonxrcl
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume vonxrcl.x: |- ( ph -> X e. Fin )
  assume vonxrcl.s: |- S = dom ( voln ` X )
  assume vonxrcl.a: |- ( ph -> A e. S )


  assert |- ( ph -> ( ( voln ` X ) ` A ) e. RR* )

  proof
    wph
    cc0
    cpnf
    cicc
    co
    cxr
    cA
    cX
    cvoln
    cfv
    cfv
    cc0
    cpnf
    iccssxr
    wph
    cA
    cS
    cX
    vonxrcl.x
    vonxrcl.s
    vonxrcl.a
    voncl
    sseldi
end
