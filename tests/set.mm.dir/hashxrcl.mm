include "wcel.mm"
include "cn0.mm"
include "cpnf.mm"
include "csn.mm"
include "cun.mm"
include "cxr.mm"
include "chash.mm"
include "cfv.mm"
include "cr.mm"
include "nn0ssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "wss.mm"
include "pnfxr.mm"
include "snssi.mm"
include "ax-mp.mm"
include "unssi.mm"
include "cvv.mm"
include "elex.mm"
include "hashf.mm"
include "ffvelrni.mm"
include "syl.mm"
include "sseldi.mm"

theorem hashxrcl
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( # ` A ) e. RR* )

  proof
    cA
    cV
    wcel
    #
    cn0
    cpnf
    csn
    #
    cun
    #
    cxr
    cA
    chash
    cfv
    #
    cn0
    @1
    cxr
    cn0
    cr
    cxr
    nn0ssre
    ressxr
    sstri
    cpnf
    cxr
    wcel
    @1
    cxr
    wss
    pnfxr
    cpnf
    cxr
    snssi
    ax-mp
    unssi
    @0
    cA
    cvv
    wcel
    @3
    @2
    wcel
    cA
    cV
    elex
    cvv
    @2
    cA
    chash
    hashf
    ffvelrni
    syl
    sseldi
end
