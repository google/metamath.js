include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cxr.mm"
include "cfv.mm"
include "iccssxr.mm"
include "meacl.mm"
include "sseldi.mm"

theorem meaxrcl
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume meaxrcl.1: |- ( ph -> M e. Meas )
  assume meaxrcl.2: |- S = dom M
  assume meaxrcl.3: |- ( ph -> A e. S )


  assert |- ( ph -> ( M ` A ) e. RR* )

  proof
    wph
    cc0
    cpnf
    cicc
    co
    cxr
    cA
    cM
    cfv
    cc0
    cpnf
    iccssxr
    wph
    cA
    cS
    cM
    meaxrcl.1
    meaxrcl.2
    meaxrcl.3
    meacl
    sseldi
end
