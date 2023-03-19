include "wcel.mm"
include "w3o.mm"
include "wsbc.mm"
include "wb.mm"
include "wo.mm"
include "idn1.mm"
include "sbcorgOLD.mm"
include "e1a.mm"
include "wal.mm"
include "df-3or.mm"
include "bicomi.mm"
include "ax-gen.mm"
include "spsbc.mm"
include "e10.mm"
include "sbcbig.mm"
include "biimpd.mm"
include "e11.mm"
include "bitr3.mm"
include "com12.mm"
include "orbi1.mm"
include "bibi1.mm"
include "biimprd.mm"
include "in1.mm"

theorem sbc3orgVD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( A e. B -> ( [. A / x ]. ( ph \/ ps \/ ch ) <-> ( [. A / x ]. ph \/ [. A / x ]. ps \/ [. A / x ]. ch ) ) )

  proof
    cA
    cB
    wcel
    #
    wph
    wps
    wch
    w3o
    #
    vx
    cA
    wsbc
    #
    wph
    vx
    cA
    wsbc
    #
    wps
    vx
    cA
    wsbc
    #
    wch
    vx
    cA
    wsbc
    #
    w3o
    #
    wb
    #
    @0
    @2
    @3
    @4
    wo
    #
    @5
    wo
    #
    wb
    #
    @9
    @6
    wb
    #
    @7
    @0
    @2
    wph
    wps
    wo
    #
    vx
    cA
    wsbc
    #
    @5
    wo
    #
    wb
    #
    @14
    @9
    wb
    #
    @10
    @0
    @12
    wch
    wo
    #
    vx
    cA
    wsbc
    #
    @14
    wb
    #
    @18
    @2
    wb
    #
    @15
    @0
    @0
    @19
    @0
    idn1
    #
    @12
    wch
    vx
    cA
    cB
    sbcorgOLD
    e1a
    @0
    @0
    @17
    @1
    wb
    #
    vx
    cA
    wsbc
    #
    @20
    @21
    @0
    @0
    @22
    vx
    wal
    @23
    @21
    @22
    vx
    @1
    @17
    wph
    wps
    wch
    df-3or
    bicomi
    ax-gen
    @22
    vx
    cA
    cB
    spsbc
    e10
    @0
    @23
    @20
    @17
    @1
    vx
    cA
    cB
    sbcbig
    biimpd
    e11
    @20
    @19
    @15
    @18
    @2
    @14
    bitr3
    com12
    e11
    @0
    @13
    @8
    wb
    #
    @16
    @0
    @0
    @24
    @21
    wph
    wps
    vx
    cA
    cB
    sbcorgOLD
    e1a
    @13
    @8
    @5
    orbi1
    e1a
    @15
    @10
    @16
    @2
    @14
    @9
    bibi1
    biimprd
    e11
    @6
    @9
    @3
    @4
    @5
    df-3or
    bicomi
    @10
    @7
    @11
    @2
    @9
    @6
    bibi1
    biimprd
    e10
    in1
end
