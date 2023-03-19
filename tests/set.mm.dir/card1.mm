include "ccrd.mm"
include "cfv.mm"
include "c1o.mm"
include "wceq.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "csn.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "com.mm"
include "wcel.mm"
include "1onn.mm"
include "cardnn.mm"
include "ax-mp.mm"
include "1n0.mm"
include "eqnetri.mm"
include "carden2a.mm"
include "mpan2.mm"
include "eqcoms.mm"
include "ensymd.mm"
include "carden2b.mm"
include "impbii.mm"
include "eqeq2i.mm"
include "en1.mm"
include "3bitr3i.mm"

theorem card1
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( ( card ` A ) = 1o <-> E. x A = { x } )

  proof
    cA
    ccrd
    cfv
    #
    c1o
    ccrd
    cfv
    #
    wceq
    #
    cA
    c1o
    cen
    wbr
    #
    @0
    c1o
    wceq
    cA
    vx
    cv
    csn
    wceq
    vx
    wex
    @2
    @3
    @2
    c1o
    cA
    c1o
    cA
    cen
    wbr
    #
    @1
    @0
    @1
    @0
    wceq
    @1
    c0
    wne
    @4
    @1
    c1o
    c0
    c1o
    com
    wcel
    @1
    c1o
    wceq
    1onn
    c1o
    cardnn
    ax-mp
    #
    1n0
    eqnetri
    c1o
    cA
    carden2a
    mpan2
    eqcoms
    ensymd
    cA
    c1o
    carden2b
    impbii
    @1
    c1o
    @0
    @5
    eqeq2i
    vx
    cA
    en1
    3bitr3i
end
