include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "cword.mm"
include "crab.mm"
include "cwwlks.mm"
include "w3a.mm"
include "wceq.mm"
include "neeq1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "fveq1.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "elrab.mm"
include "wwlks.mm"
include "eleq2i.mm"
include "3anan12.mm"
include "3bitr4i.mm"

theorem iswwlks
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cV: class V
  let cW: class W
  let vg: setvar g
  let vw: setvar w
  assume wwlks.v: |- V = ( Vtx ` G )
  assume wwlks.e: |- E = ( Edg ` G )

  disjoint G i
  disjoint W i
  disjoint E g
  disjoint G g
  disjoint G w
  disjoint g i
  disjoint g w
  disjoint i w
  disjoint V g
  disjoint V w
  disjoint E w
  disjoint W w
  assert |- ( W e. ( WWalks ` G ) <-> ( W =/= (/) /\ W e. Word V /\ A. i e. ( 0 ..^ ( ( # ` W ) - 1 ) ) { ( W ` i ) , ( W ` ( i + 1 ) ) } e. E ) )

  proof
    cW
    vw
    cv
    #
    c0
    wne
    #
    vi
    cv
    #
    @0
    cfv
    #
    @2
    c1
    caddc
    co
    #
    @0
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    vi
    cc0
    @0
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    wa
    #
    vw
    cV
    cword
    #
    crab
    #
    wcel
    cW
    @13
    wcel
    #
    cW
    c0
    wne
    #
    @2
    cW
    cfv
    #
    @4
    cW
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    vi
    cc0
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    wa
    #
    wa
    cW
    cG
    cwwlks
    cfv
    #
    wcel
    @16
    @15
    @24
    w3a
    @12
    @25
    vw
    cW
    @13
    @0
    cW
    wceq
    #
    @1
    @16
    @11
    @24
    @0
    cW
    c0
    neeq1
    @27
    @7
    @20
    vi
    @10
    @23
    @27
    @9
    @22
    cc0
    cfzo
    @27
    @8
    @21
    c1
    cmin
    @0
    cW
    chash
    fveq2
    oveq1d
    oveq2d
    @27
    @6
    @19
    cE
    @27
    @3
    @17
    @5
    @18
    @2
    @0
    cW
    fveq1
    @4
    @0
    cW
    fveq1
    preq12d
    eleq1d
    raleqbidv
    anbi12d
    elrab
    @26
    @14
    cW
    vw
    vi
    cE
    cG
    cV
    wwlks.v
    wwlks.e
    wwlks
    eleq2i
    @16
    @15
    @24
    3anan12
    3bitr4i
end
