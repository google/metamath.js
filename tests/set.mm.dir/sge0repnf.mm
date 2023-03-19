include "csumge0.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wceq.mm"
include "wn.mm"
include "wi.mm"
include "renepnf.mm"
include "neneqd.mm"
include "a1i.mm"
include "wa.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "rge0ssre.mm"
include "cxr.mm"
include "0xr.mm"
include "pnfxr.mm"
include "sge0xrcl.mm"
include "adantr.mm"
include "cle.mm"
include "wbr.mm"
include "sge0ge0.mm"
include "clt.mm"
include "simpr.mm"
include "wb.mm"
include "nltpnft.mm"
include "syl.mm"
include "mtbid.mm"
include "notnotrd.mm"
include "elicod.mm"
include "sseldi.mm"
include "ex.mm"
include "impbid.mm"

theorem sge0repnf
  let wph: wff ph
  let cF: class F
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume sge0repnf.x: |- ( ph -> X e. V )
  assume sge0repnf.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )


  assert |- ( ph -> ( ( sum^ ` F ) e. RR <-> -. ( sum^ ` F ) = +oo ) )

  proof
    wph
    cF
    csumge0
    cfv
    #
    cr
    wcel
    #
    @0
    cpnf
    wceq
    #
    wn
    #
    @1
    @3
    wi
    wph
    @1
    @0
    cpnf
    @0
    renepnf
    neneqd
    a1i
    wph
    @3
    @1
    wph
    @3
    wa
    #
    cc0
    cpnf
    cico
    co
    cr
    @0
    rge0ssre
    @4
    cc0
    cpnf
    @0
    cc0
    cxr
    wcel
    @4
    0xr
    a1i
    cpnf
    cxr
    wcel
    @4
    pnfxr
    a1i
    wph
    @0
    cxr
    wcel
    #
    @3
    wph
    cF
    cV
    cX
    sge0repnf.x
    sge0repnf.f
    sge0xrcl
    #
    adantr
    wph
    cc0
    @0
    cle
    wbr
    @3
    wph
    cF
    cV
    cX
    sge0repnf.x
    sge0repnf.f
    sge0ge0
    adantr
    @4
    @0
    cpnf
    clt
    wbr
    #
    @4
    @2
    @7
    wn
    #
    wph
    @3
    simpr
    wph
    @2
    @8
    wb
    #
    @3
    wph
    @5
    @9
    @6
    @0
    nltpnft
    syl
    adantr
    mtbid
    notnotrd
    elicod
    sseldi
    ex
    impbid
end
