include "cres.mm"
include "csumge0.mm"
include "cfv.mm"
include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cvv.mm"
include "cin.mm"
include "inex1g.mm"
include "syl.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "fresin.mm"
include "sge0xrcl.mm"
include "mnfxr.mm"
include "a1i.mm"
include "0xr.mm"
include "mnflt0.mm"
include "sge0ge0.mm"
include "xrltletrd.mm"
include "sge0less.mm"
include "xrre.mm"
include "syl22anc.mm"

theorem sge0ssre
  let wph: wff ph
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume sge0less.x: |- ( ph -> X e. V )
  assume sge0less.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )
  assume sge0ssre.re: |- ( ph -> ( sum^ ` F ) e. RR )


  assert |- ( ph -> ( sum^ ` ( F |` Y ) ) e. RR )

  proof
    wph
    cF
    cY
    cres
    #
    csumge0
    cfv
    #
    cxr
    wcel
    cF
    csumge0
    cfv
    #
    cr
    wcel
    cmnf
    @1
    clt
    wbr
    @1
    @2
    cle
    wbr
    @1
    cr
    wcel
    wph
    @0
    cvv
    cX
    cY
    cin
    #
    wph
    cX
    cV
    wcel
    @3
    cvv
    wcel
    sge0less.x
    cX
    cY
    cV
    inex1g
    syl
    #
    wph
    cX
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    @3
    @5
    @0
    wf
    sge0less.f
    cX
    @5
    cF
    cY
    fresin
    syl
    #
    sge0xrcl
    #
    sge0ssre.re
    wph
    cmnf
    cc0
    @1
    cmnf
    cxr
    wcel
    wph
    mnfxr
    a1i
    cc0
    cxr
    wcel
    wph
    0xr
    a1i
    @7
    cmnf
    cc0
    clt
    wbr
    wph
    mnflt0
    a1i
    wph
    @0
    cvv
    @3
    @4
    @6
    sge0ge0
    xrltletrd
    wph
    cF
    cV
    cX
    cY
    sge0less.x
    sge0less.f
    sge0less
    @1
    @2
    xrre
    syl22anc
end
