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
include "clsw.mm"
include "w3a.mm"
include "cword.mm"
include "crab.mm"
include "wa.mm"
include "cclwwlk.mm"
include "wceq.mm"
include "neeq1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "fveq1.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "raleqbidv.mm"
include "3anbi123d.mm"
include "elrab.mm"
include "clwwlk.mm"
include "eleq2i.mm"
include "3anass.mm"
include "anass.mm"
include "bicomi.mm"
include "anbi2i.mm"
include "3bitri.mm"
include "3bitr4i.mm"

theorem isclwwlk
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cV: class V
  let cW: class W
  let vg: setvar g
  let vw: setvar w
  assume clwwlk.v: |- V = ( Vtx ` G )
  assume clwwlk.e: |- E = ( Edg ` G )

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
  assert |- ( W e. ( ClWWalks ` G ) <-> ( ( W e. Word V /\ W =/= (/) ) /\ A. i e. ( 0 ..^ ( ( # ` W ) - 1 ) ) { ( W ` i ) , ( W ` ( i + 1 ) ) } e. E /\ { ( lastS ` W ) , ( W ` 0 ) } e. E ) )

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
    @0
    clsw
    cfv
    #
    cc0
    @0
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    vw
    cV
    cword
    #
    crab
    #
    wcel
    cW
    @17
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
    cW
    clsw
    cfv
    #
    cc0
    cW
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    wa
    #
    cW
    cG
    cclwwlk
    cfv
    #
    wcel
    @19
    @20
    wa
    #
    @28
    @32
    w3a
    #
    @16
    @33
    vw
    cW
    @17
    @0
    cW
    wceq
    #
    @1
    @20
    @11
    @28
    @15
    @32
    @0
    cW
    c0
    neeq1
    @38
    @7
    @24
    vi
    @10
    @27
    @38
    @9
    @26
    cc0
    cfzo
    @38
    @8
    @25
    c1
    cmin
    @0
    cW
    chash
    fveq2
    oveq1d
    oveq2d
    @38
    @6
    @23
    cE
    @38
    @3
    @21
    @5
    @22
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
    @38
    @14
    @31
    cE
    @38
    @12
    @29
    @13
    @30
    @0
    cW
    clsw
    fveq2
    cc0
    @0
    cW
    fveq1
    preq12d
    eleq1d
    3anbi123d
    elrab
    @35
    @18
    cW
    vw
    vi
    cE
    cG
    cV
    clwwlk.v
    clwwlk.e
    clwwlk
    eleq2i
    @37
    @36
    @28
    @32
    wa
    #
    wa
    @19
    @20
    @39
    wa
    #
    wa
    @34
    @36
    @28
    @32
    3anass
    @19
    @20
    @39
    anass
    @40
    @33
    @19
    @33
    @40
    @20
    @28
    @32
    3anass
    bicomi
    anbi2i
    3bitri
    3bitr4i
end
