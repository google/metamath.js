include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "csupp.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-supp.mm"
include "a1i.mm"
include "dmeq.mm"
include "adantr.mm"
include "imaeq1.mm"
include "sneq.mm"
include "adantl.mm"
include "neeq12d.mm"
include "rabeqbidv.mm"
include "elex.mm"
include "dmexg.mm"
include "rabexg.mm"
include "syl.mm"
include "ovmpt2d.mm"

theorem suppval
  let vi: setvar i
  let cV: class V
  let cW: class W
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  let vz: setvar z

  disjoint X i
  disjoint Z i
  disjoint V x
  disjoint V z
  disjoint x z
  disjoint W x
  disjoint W z
  disjoint X x
  disjoint X z
  disjoint i x
  disjoint i z
  disjoint Z x
  disjoint Z z
  assert |- ( ( X e. V /\ Z e. W ) -> ( X supp Z ) = { i e. dom X | ( X " { i } ) =/= { Z } } )

  proof
    cX
    cV
    wcel
    #
    cZ
    cW
    wcel
    #
    wa
    #
    vx
    vz
    cX
    cZ
    cvv
    cvv
    vx
    cv
    #
    vi
    cv
    csn
    #
    cima
    #
    vz
    cv
    #
    csn
    #
    wne
    #
    vi
    @3
    cdm
    #
    crab
    #
    cX
    @4
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
    csupp
    cvv
    csupp
    vx
    vz
    cvv
    cvv
    @10
    cmpt2
    wceq
    @2
    vx
    vz
    vi
    df-supp
    a1i
    @3
    cX
    wceq
    #
    @6
    cZ
    wceq
    #
    wa
    #
    @10
    @15
    wceq
    @2
    @18
    @8
    @13
    vi
    @9
    @14
    @16
    @9
    @14
    wceq
    @17
    @3
    cX
    dmeq
    adantr
    @18
    @5
    @11
    @7
    @12
    @16
    @5
    @11
    wceq
    @17
    @3
    cX
    @4
    imaeq1
    adantr
    @17
    @7
    @12
    wceq
    @16
    @6
    cZ
    sneq
    adantl
    neeq12d
    rabeqbidv
    adantl
    @0
    cX
    cvv
    wcel
    @1
    cX
    cV
    elex
    adantr
    @1
    cZ
    cvv
    wcel
    @0
    cZ
    cW
    elex
    adantl
    @2
    @14
    cvv
    wcel
    #
    @15
    cvv
    wcel
    @0
    @19
    @1
    cX
    cV
    dmexg
    adantr
    @13
    vi
    @14
    cvv
    rabexg
    syl
    ovmpt2d
end
