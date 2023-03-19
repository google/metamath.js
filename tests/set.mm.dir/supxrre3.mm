include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wcel.mm"
include "cpnf.mm"
include "wbr.mm"
include "cv.mm"
include "cle.mm"
include "wral.mm"
include "wrex.mm"
include "supxrre1.mm"
include "wb.mm"
include "id.mm"
include "rexr.mm"
include "ssriv.mm"
include "a1i.mm"
include "sstrd.mm"
include "supxrbnd2.mm"
include "syl.mm"
include "bicomd.mm"
include "adantr.mm"
include "bitrd.mm"

theorem supxrre3
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( ( A C_ RR /\ A =/= (/) ) -> ( sup ( A , RR* , < ) e. RR <-> E. x e. RR A. y e. A y <_ x ) )

  proof
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    wa
    cA
    cxr
    clt
    csup
    #
    cr
    wcel
    @2
    cpnf
    clt
    wbr
    #
    vy
    cv
    vx
    cv
    #
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    #
    cA
    supxrre1
    @0
    @3
    @5
    wb
    @1
    @0
    @5
    @3
    @0
    cA
    cxr
    wss
    @5
    @3
    wb
    @0
    cA
    cr
    cxr
    @0
    id
    cr
    cxr
    wss
    @0
    vx
    cr
    cxr
    @4
    rexr
    ssriv
    a1i
    sstrd
    vx
    vy
    cA
    supxrbnd2
    syl
    bicomd
    adantr
    bitrd
end
