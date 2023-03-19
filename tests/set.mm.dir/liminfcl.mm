include "wcel.mm"
include "clsi.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "cinf.mm"
include "cmpt.mm"
include "crn.mm"
include "csup.mm"
include "eqid.mm"
include "liminfval.mm"
include "nfv.mm"
include "wa.mm"
include "wss.mm"
include "inss2.mm"
include "infxrcl.mm"
include "ax-mp.mm"
include "a1i.mm"
include "rnmptssd.mm"
include "supxrcld.mm"
include "eqeltrd.mm"

theorem liminfcl
  let cF: class F
  let cV: class V
  let vk: setvar k
  let vx: setvar x


  assert |- ( F e. V -> ( liminf ` F ) e. RR* )

  proof
    cF
    cV
    wcel
    #
    cF
    clsi
    cfv
    vk
    cr
    cF
    vk
    cv
    #
    cpnf
    cico
    co
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    cinf
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    cxr
    vk
    cF
    @5
    cV
    @5
    eqid
    #
    liminfval
    @0
    @6
    @0
    vk
    cr
    @4
    cxr
    @5
    @0
    vk
    nfv
    @7
    @4
    cxr
    wcel
    #
    @0
    @1
    cr
    wcel
    wa
    @3
    cxr
    wss
    @8
    @2
    cxr
    inss2
    @3
    infxrcl
    ax-mp
    a1i
    rnmptssd
    supxrcld
    eqeltrd
end
