include "wfun.mm"
include "wcel.mm"
include "w3a.mm"
include "csupp.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "cfv.mm"
include "wceq.mm"
include "suppval.mm"
include "3adant1.mm"
include "wa.mm"
include "wfn.mm"
include "funfn.mm"
include "biimpi.mm"
include "3ad2ant1.mm"
include "fnsnfv.mm"
include "sylan.mm"
include "eqcomd.mm"
include "neeq1d.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "sneqbg.mm"
include "mp1i.mm"
include "necon3bid.mm"
include "bitrd.mm"
include "rabbidva.mm"
include "eqtrd.mm"

theorem suppval1
  let vi: setvar i
  let cV: class V
  let cW: class W
  let cX: class X
  let cZ: class Z

  disjoint V i
  disjoint W i
  disjoint X i
  disjoint Z i
  assert |- ( ( Fun X /\ X e. V /\ Z e. W ) -> ( X supp Z ) = { i e. dom X | ( X ` i ) =/= Z } )

  proof
    cX
    wfun
    #
    cX
    cV
    wcel
    #
    cZ
    cW
    wcel
    #
    w3a
    #
    cX
    cZ
    csupp
    co
    #
    cX
    vi
    cv
    #
    csn
    cima
    #
    cZ
    csn
    #
    wne
    #
    vi
    cX
    cdm
    #
    crab
    #
    @5
    cX
    cfv
    #
    cZ
    wne
    #
    vi
    @9
    crab
    @1
    @2
    @4
    @10
    wceq
    @0
    vi
    cV
    cW
    cX
    cZ
    suppval
    3adant1
    @3
    @8
    @12
    vi
    @9
    @3
    @5
    @9
    wcel
    #
    wa
    #
    @8
    @11
    csn
    #
    @7
    wne
    @12
    @14
    @6
    @15
    @7
    @14
    @15
    @6
    @3
    cX
    @9
    wfn
    #
    @13
    @15
    @6
    wceq
    @0
    @1
    @16
    @2
    @0
    @16
    cX
    funfn
    biimpi
    3ad2ant1
    @9
    @5
    cX
    fnsnfv
    sylan
    eqcomd
    neeq1d
    @14
    @15
    @7
    @11
    cZ
    @11
    cvv
    wcel
    @15
    @7
    wceq
    @11
    cZ
    wceq
    wb
    @14
    @5
    cX
    fvex
    @11
    cZ
    cvv
    sneqbg
    mp1i
    necon3bid
    bitrd
    rabbidva
    eqtrd
end
