include "cxr.mm"
include "cv.mm"
include "cpnf.mm"
include "cioc.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cmnf.mm"
include "cico.mm"
include "cun.mm"
include "cioo.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "ctg.mm"
include "ctb.mm"
include "wcel.mm"
include "wss.mm"
include "ctop.mm"
include "eqid.mm"
include "leordtval.mm"
include "letop.mm"
include "eqeltrri.mm"
include "tgclb.mm"
include "mpbir.mm"
include "bastg.mm"
include "ax-mp.mm"
include "sseqtr4i.mm"
include "ssun2.mm"
include "ioorebas.mm"
include "sselii.mm"

theorem iooordt
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A (,) B ) e. ( ordTop ` <_ )

  proof
    vx
    cxr
    vx
    cv
    #
    cpnf
    cioc
    co
    cmpt
    crn
    #
    vx
    cxr
    cmnf
    @0
    cico
    co
    cmpt
    crn
    #
    cun
    #
    cioo
    crn
    #
    cun
    #
    cle
    cordt
    cfv
    #
    cA
    cB
    cioo
    co
    #
    @5
    @5
    ctg
    cfv
    #
    @6
    @5
    ctb
    wcel
    #
    @5
    @8
    wss
    @9
    @8
    ctop
    wcel
    @6
    @8
    ctop
    vx
    @1
    @2
    @4
    @1
    eqid
    @2
    eqid
    @4
    eqid
    leordtval
    #
    letop
    eqeltrri
    @5
    tgclb
    mpbir
    @5
    ctb
    bastg
    ax-mp
    @10
    sseqtr4i
    @4
    @5
    @7
    @4
    @3
    ssun2
    cA
    cB
    ioorebas
    sselii
    sselii
end
