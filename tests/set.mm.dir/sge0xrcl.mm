include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cxr.mm"
include "csumge0.mm"
include "cfv.mm"
include "iccssxr.mm"
include "sge0cl.mm"
include "sseldi.mm"

theorem sge0xrcl
  let wph: wff ph
  let cF: class F
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume sge0xrcl.x: |- ( ph -> X e. V )
  assume sge0xrcl.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )


  assert |- ( ph -> ( sum^ ` F ) e. RR* )

  proof
    wph
    cc0
    cpnf
    cicc
    co
    cxr
    cF
    csumge0
    cfv
    cc0
    cpnf
    iccssxr
    wph
    cF
    cV
    cX
    sge0xrcl.x
    sge0xrcl.f
    sge0cl
    sseldi
end
