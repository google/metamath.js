include "cv.mm"
include "wss.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cvv.mm"
include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "cin.mm"
include "wrex.mm"
include "wn.mm"
include "ssindif0.mm"
include "sseq1.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "spv.mm"
include "syl5bir.mm"
include "eldifn.mm"
include "nsyli.mm"
include "imp.mm"
include "nrexdv.mm"
include "zfregs.mm"
include "necon1bi.mm"
include "syl.mm"
include "vdif0.mm"
include "sylibr.mm"

theorem setind
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A. x ( x C_ A -> x e. A ) -> A = _V )

  proof
    vx
    cv
    #
    cA
    wss
    #
    @0
    cA
    wcel
    #
    wi
    #
    vx
    wal
    #
    cvv
    cA
    cdif
    #
    c0
    wceq
    #
    cA
    cvv
    wceq
    @4
    vy
    cv
    #
    @5
    cin
    c0
    wceq
    #
    vy
    @5
    wrex
    #
    wn
    @6
    @4
    @8
    vy
    @5
    @4
    @7
    @5
    wcel
    #
    @8
    wn
    @4
    @8
    @7
    cA
    wcel
    #
    @10
    @8
    @7
    cA
    wss
    #
    @4
    @11
    @7
    cA
    ssindif0
    @3
    @12
    @11
    wi
    vx
    vy
    @0
    @7
    wceq
    @1
    @12
    @2
    @11
    @0
    @7
    cA
    sseq1
    @0
    @7
    cA
    eleq1
    imbi12d
    spv
    syl5bir
    @7
    cvv
    cA
    eldifn
    nsyli
    imp
    nrexdv
    @9
    @5
    c0
    vy
    @5
    zfregs
    necon1bi
    syl
    cA
    vdif0
    sylibr
end
