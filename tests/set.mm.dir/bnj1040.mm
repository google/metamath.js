include "cv.mm"
include "wsbc.mm"
include "wcel.mm"
include "wfn.mm"
include "w-bnj17.mm"
include "sbcbii.mm"
include "w3a.mm"
include "wa.mm"
include "df-bnj17.mm"
include "vex.mm"
include "bnj525.mm"
include "bicomi.mm"
include "bnj887.mm"
include "sbcan.mm"
include "sbc3an.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "3bitr4ri.mm"

theorem bnj1040
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cD: class D
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  assume bnj1040.1: |- ( ph' <-> [. j / i ]. ph )
  assume bnj1040.2: |- ( ps' <-> [. j / i ]. ps )
  assume bnj1040.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1040.4: |- ( ch' <-> [. j / i ]. ch )

  disjoint D i
  disjoint f i
  disjoint i n
  assert |- ( ch' <-> ( n e. D /\ f Fn n /\ ph' /\ ps' ) )

  proof
    bnjwchm
    wch
    vi
    vj
    cv
    #
    wsbc
    vn
    cv
    #
    cD
    wcel
    #
    vf
    cv
    @1
    wfn
    #
    wph
    wps
    w-bnj17
    #
    vi
    @0
    wsbc
    #
    @2
    @3
    bnjwphm
    bnjwpsm
    w-bnj17
    #
    bnj1040.4
    wch
    @4
    vi
    @0
    bnj1040.3
    sbcbii
    @2
    vi
    @0
    wsbc
    #
    @3
    vi
    @0
    wsbc
    #
    wph
    vi
    @0
    wsbc
    #
    wps
    vi
    @0
    wsbc
    #
    w-bnj17
    @7
    @8
    @9
    w3a
    #
    @10
    wa
    #
    @6
    @5
    @7
    @8
    @9
    @10
    df-bnj17
    @2
    @3
    bnjwphm
    bnjwpsm
    @7
    @8
    @9
    @10
    @7
    @2
    @2
    vi
    @0
    vj
    vex
    #
    bnj525
    bicomi
    @8
    @3
    @3
    vi
    @0
    @13
    bnj525
    bicomi
    bnj1040.1
    bnj1040.2
    bnj887
    @5
    @2
    @3
    wph
    w3a
    #
    wps
    wa
    #
    vi
    @0
    wsbc
    @14
    vi
    @0
    wsbc
    #
    @10
    wa
    @12
    @4
    @15
    vi
    @0
    @2
    @3
    wph
    wps
    df-bnj17
    sbcbii
    @14
    wps
    vi
    @0
    sbcan
    @16
    @11
    @10
    @2
    @3
    wph
    vi
    @0
    sbc3an
    anbi1i
    3bitri
    3bitr4ri
    3bitri
end
