include "wcel.mm"
include "cvv.mm"
include "clsp.mm"
include "cfv.mm"
include "cxr.mm"
include "elex.mm"
include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cin.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "crn.mm"
include "cinf.mm"
include "df-limsup.mm"
include "wss.mm"
include "wf.mm"
include "eqid.mm"
include "inss2.mm"
include "supxrcl.mm"
include "mp1i.mm"
include "fmpti.mm"
include "frn.mm"
include "ax-mp.mm"
include "infxrcl.mm"
include "ffvelrni.mm"
include "syl.mm"

theorem limsupcl
  let cF: class F
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  let cA: class A
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vf: setvar f


  assert |- ( F e. V -> ( limsup ` F ) e. RR* )

  proof
    cF
    cV
    wcel
    cF
    cvv
    wcel
    cF
    clsp
    cfv
    cxr
    wcel
    cF
    cV
    elex
    cvv
    cxr
    cF
    clsp
    vf
    cvv
    cxr
    vk
    cr
    vf
    cv
    #
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
    csup
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    clsp
    vf
    vk
    df-limsup
    @6
    cxr
    wss
    #
    @7
    cxr
    wcel
    @0
    cvv
    wcel
    cr
    cxr
    @5
    wf
    @8
    vk
    cr
    cxr
    @4
    @5
    @5
    eqid
    @3
    cxr
    wss
    @4
    cxr
    wcel
    @1
    cr
    wcel
    @2
    cxr
    inss2
    @3
    supxrcl
    mp1i
    fmpti
    cr
    cxr
    @5
    frn
    ax-mp
    @6
    infxrcl
    mp1i
    fmpti
    ffvelrni
    syl
end
