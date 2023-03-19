include "cc0.mm"
include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "csumge0.mm"
include "cfv.mm"
include "cicc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "sge0cl.mm"
include "iccgelb.mm"
include "syl3anc.mm"

theorem sge0ge0
  let wph: wff ph
  let cF: class F
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume sge0ge0.x: |- ( ph -> X e. V )
  assume sge0ge0.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )


  assert |- ( ph -> 0 <_ ( sum^ ` F ) )

  proof
    wph
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    cF
    csumge0
    cfv
    #
    cc0
    cpnf
    cicc
    co
    wcel
    cc0
    @2
    cle
    wbr
    @0
    wph
    0xr
    a1i
    @1
    wph
    pnfxr
    a1i
    wph
    cF
    cV
    cX
    sge0ge0.x
    sge0ge0.f
    sge0cl
    cc0
    cpnf
    @2
    iccgelb
    syl3anc
end
