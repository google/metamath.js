include "wsbc.mm"
include "cv.mm"
include "wcel.mm"
include "wfn.mm"
include "w-bnj17.mm"
include "sbcco.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "bnj252.mm"
include "sbcbii.mm"
include "vex.mm"
include "bnj525.mm"
include "sbc3an.mm"
include "bnj62.mm"
include "3anbi1i.mm"
include "bitri.mm"
include "anbi12i.mm"
include "sbcan.mm"
include "3bitr4ri.mm"
include "3bitr4i.mm"
include "fneq1.mm"
include "sbceq1a.mm"
include "bitr4i.mm"
include "syl6bbr.mm"
include "3anbi123d.mm"
include "anbi2d.mm"
include "3bitr4g.mm"
include "syl5bb.mm"
include "sbcie.mm"
include "3bitr2i.mm"

theorem bnj976
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cD: class D
  let vf: setvar f
  let cG: class G
  let cN: class N
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  let vh: setvar h
  assume bnj976.1: |- ( ch <-> ( N e. D /\ f Fn N /\ ph /\ ps ) )
  assume bnj976.2: |- ( ph' <-> [. G / f ]. ph )
  assume bnj976.3: |- ( ps' <-> [. G / f ]. ps )
  assume bnj976.4: |- ( ch' <-> [. G / f ]. ch )
  assume bnj976.5: |- G e. _V

  disjoint D f
  disjoint N f
  disjoint D h
  disjoint f h
  disjoint G h
  disjoint N h
  disjoint ch h
  disjoint h ph
  disjoint h ph'
  disjoint h ps
  disjoint h ps'
  assert |- ( ch' <-> ( N e. D /\ G Fn N /\ ph' /\ ps' ) )

  proof
    bnjwchm
    wch
    vf
    cG
    wsbc
    wch
    vf
    vh
    cv
    #
    wsbc
    #
    vh
    cG
    wsbc
    cN
    cD
    wcel
    #
    cG
    cN
    wfn
    #
    bnjwphm
    bnjwpsm
    w-bnj17
    #
    bnj976.4
    wch
    vf
    vh
    cG
    sbcco
    @1
    @4
    vh
    cG
    bnj976.5
    @1
    @2
    @0
    cN
    wfn
    #
    wph
    vf
    @0
    wsbc
    #
    wps
    vf
    @0
    wsbc
    #
    w-bnj17
    #
    @0
    cG
    wceq
    #
    @4
    @2
    vf
    cv
    cN
    wfn
    #
    wph
    wps
    w-bnj17
    #
    vf
    @0
    wsbc
    @2
    @10
    wph
    wps
    w3a
    #
    wa
    #
    vf
    @0
    wsbc
    #
    @1
    @8
    @11
    @13
    vf
    @0
    @2
    @10
    wph
    wps
    bnj252
    sbcbii
    wch
    @11
    vf
    @0
    bnj976.1
    sbcbii
    @2
    vf
    @0
    wsbc
    #
    @12
    vf
    @0
    wsbc
    #
    wa
    @2
    @5
    @6
    @7
    w3a
    #
    wa
    #
    @14
    @8
    @15
    @2
    @16
    @17
    @2
    vf
    @0
    vh
    vex
    bnj525
    @16
    @10
    vf
    @0
    wsbc
    #
    @6
    @7
    w3a
    @17
    @10
    wph
    wps
    vf
    @0
    sbc3an
    @19
    @5
    @6
    @7
    vf
    vh
    cN
    bnj62
    3anbi1i
    bitri
    anbi12i
    @2
    @12
    vf
    @0
    sbcan
    @2
    @5
    @6
    @7
    bnj252
    #
    3bitr4ri
    3bitr4i
    @9
    @18
    @2
    @3
    bnjwphm
    bnjwpsm
    w3a
    #
    wa
    @8
    @4
    @9
    @17
    @21
    @2
    @9
    @5
    @3
    @6
    bnjwphm
    @7
    bnjwpsm
    cN
    @0
    cG
    fneq1
    @9
    @6
    @6
    vh
    cG
    wsbc
    #
    bnjwphm
    @6
    vh
    cG
    sbceq1a
    bnjwphm
    wph
    vf
    cG
    wsbc
    @22
    bnj976.2
    wph
    vf
    vh
    cG
    sbcco
    bitr4i
    syl6bbr
    @9
    @7
    @7
    vh
    cG
    wsbc
    #
    bnjwpsm
    @7
    vh
    cG
    sbceq1a
    bnjwpsm
    wps
    vf
    cG
    wsbc
    @23
    bnj976.3
    wps
    vf
    vh
    cG
    sbcco
    bitr4i
    syl6bbr
    3anbi123d
    anbi2d
    @20
    @2
    @3
    bnjwphm
    bnjwpsm
    bnj252
    3bitr4g
    syl5bb
    sbcie
    3bitr2i
end
