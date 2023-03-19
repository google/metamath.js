include "wcel.mm"
include "cspr.mm"
include "cfv.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "cpw.mm"
include "crab.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "sprvalpw.mm"
include "wa.mm"
include "wne.mm"
include "wi.mm"
include "id.mm"
include "vex.mm"
include "prnz.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "rexlimivv.mm"
include "adantl.mm"
include "pm4.71ri.mm"
include "ancom.mm"
include "anbi1i.mm"
include "anass.mm"
include "eldifsn.mm"
include "bicomi.mm"
include "3bitr3i.mm"
include "bitri.mm"
include "rabbia2.mm"
include "syl6eq.mm"

theorem sprvalpwn0
  let cV: class V
  let cW: class W
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vx: setvar x

  disjoint V a
  disjoint V b
  disjoint V p
  disjoint a b
  disjoint a p
  disjoint b p
  disjoint W a
  disjoint W b
  disjoint W p
  disjoint k x
  assert |- ( V e. W -> ( Pairs ` V ) = { p e. ( ~P V \ { (/) } ) | E. a e. V E. b e. V p = { a , b } } )

  proof
    cV
    cW
    wcel
    cV
    cspr
    cfv
    vp
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    cpr
    #
    wceq
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    vp
    cV
    cpw
    #
    crab
    @5
    vp
    @6
    c0
    csn
    cdif
    #
    crab
    cV
    cW
    vp
    va
    vb
    sprvalpw
    @5
    @5
    vp
    @6
    @7
    @0
    @6
    wcel
    #
    @5
    wa
    #
    @0
    c0
    wne
    #
    @9
    wa
    #
    @0
    @7
    wcel
    #
    @5
    wa
    #
    @9
    @10
    @5
    @10
    @8
    @4
    @10
    va
    vb
    cV
    cV
    @4
    @10
    wi
    @1
    cV
    wcel
    @2
    cV
    wcel
    wa
    @4
    @0
    @3
    c0
    @4
    id
    @3
    c0
    wne
    @4
    @1
    @2
    va
    vex
    prnz
    a1i
    eqnetrd
    a1i
    rexlimivv
    adantl
    pm4.71ri
    @10
    @8
    wa
    #
    @5
    wa
    @8
    @10
    wa
    #
    @5
    wa
    @11
    @13
    @14
    @15
    @5
    @10
    @8
    ancom
    anbi1i
    @10
    @8
    @5
    anass
    @15
    @12
    @5
    @12
    @15
    @0
    @6
    c0
    eldifsn
    bicomi
    anbi1i
    3bitr3i
    bitri
    rabbia2
    syl6eq
end
