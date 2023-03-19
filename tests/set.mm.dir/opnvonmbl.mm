include "cv.mm"
include "cico.mm"
include "ccom.mm"
include "cfv.mm"
include "cixp.mm"
include "wss.mm"
include "cq.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "wceq.mm"
include "fveq2.mm"
include "cbvixpv.mm"
include "a1i.mm"
include "coeq2.mm"
include "fveq1d.mm"
include "ixpeq2dv.mm"
include "eqtrd.mm"
include "sseq1d.mm"
include "cbvrabv.mm"
include "opnvonmbllem2.mm"

theorem opnvonmbl
  let wph: wff ph
  let cS: class S
  let cG: class G
  let cX: class X
  let vf: setvar f
  let vh: setvar h
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x
  assume opnvonmbl.x: |- ( ph -> X e. Fin )
  assume opnvonmbl.s: |- S = dom ( voln ` X )
  assume opnvonmbl.g: |- ( ph -> G e. ( TopOpen ` ( RR^ ` X ) ) )


  assert |- ( ph -> G e. S )

  proof
    wph
    cS
    vh
    vi
    cG
    vk
    cX
    vk
    cv
    #
    cico
    vf
    cv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    cG
    wss
    #
    vf
    cq
    cq
    cxp
    cX
    cmap
    co
    #
    crab
    cX
    opnvonmbl.x
    opnvonmbl.s
    opnvonmbl.g
    @5
    vi
    cX
    vi
    cv
    #
    cico
    vh
    cv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    cG
    wss
    vf
    vh
    @6
    @1
    @8
    wceq
    #
    @4
    @11
    cG
    @12
    @4
    vi
    cX
    @7
    @2
    cfv
    #
    cixp
    #
    @11
    @4
    @14
    wceq
    @12
    vk
    vi
    cX
    @3
    @13
    @0
    @7
    @2
    fveq2
    cbvixpv
    a1i
    @12
    vi
    cX
    @13
    @10
    @12
    @7
    @2
    @9
    @1
    @8
    cico
    coeq2
    fveq1d
    ixpeq2dv
    eqtrd
    sseq1d
    cbvrabv
    opnvonmbllem2
end
