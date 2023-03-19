include "wfn.mm"
include "wcel.mm"
include "w3a.mm"
include "csupp.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "wfun.mm"
include "cvv.mm"
include "wceq.mm"
include "fnfun.mm"
include "3ad2ant1.mm"
include "fnex.mm"
include "3adant3.mm"
include "simp3.mm"
include "suppval1.mm"
include "syl3anc.mm"
include "fndm.mm"
include "rabeq.mm"
include "syl.mm"
include "eqtrd.mm"

theorem suppvalfn
  let vi: setvar i
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cZ: class Z

  disjoint V i
  disjoint W i
  disjoint X i
  disjoint Z i
  disjoint F i
  assert |- ( ( F Fn X /\ X e. V /\ Z e. W ) -> ( F supp Z ) = { i e. X | ( F ` i ) =/= Z } )

  proof
    cF
    cX
    wfn
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
    cF
    cZ
    csupp
    co
    #
    vi
    cv
    cF
    cfv
    cZ
    wne
    #
    vi
    cF
    cdm
    #
    crab
    #
    @5
    vi
    cX
    crab
    #
    @3
    cF
    wfun
    #
    cF
    cvv
    wcel
    #
    @2
    @4
    @7
    wceq
    @0
    @1
    @9
    @2
    cX
    cF
    fnfun
    3ad2ant1
    @0
    @1
    @10
    @2
    cX
    cV
    cF
    fnex
    3adant3
    @0
    @1
    @2
    simp3
    vi
    cvv
    cW
    cF
    cZ
    suppval1
    syl3anc
    @3
    @6
    cX
    wceq
    #
    @7
    @8
    wceq
    @0
    @1
    @11
    @2
    cX
    cF
    fndm
    3ad2ant1
    @5
    vi
    @6
    cX
    rabeq
    syl
    eqtrd
end
