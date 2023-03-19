include "coprab.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "3exbidv.mm"
include "df-oprab.mm"
include "elab2g.mm"
include "ibi.mm"
include "c1st.mm"
include "cfv.mm"
include "wb.mm"
include "opex.mm"
include "vex.mm"
include "op1std.mm"
include "fveq2d.mm"
include "op1st.mm"
include "syl6req.mm"
include "syl.mm"
include "c2nd.mm"
include "op2nd.mm"
include "op2ndd.mm"
include "eqcomd.mm"
include "3bitrd.mm"
include "biimpa.mm"
include "exlimiv.mm"

theorem eloprabi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  assume eloprabi.1: |- ( x = ( 1st ` ( 1st ` A ) ) -> ( ph <-> ps ) )
  assume eloprabi.2: |- ( y = ( 2nd ` ( 1st ` A ) ) -> ( ps <-> ch ) )
  assume eloprabi.3: |- ( z = ( 2nd ` A ) -> ( ch <-> th ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint th x
  disjoint th y
  disjoint th z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint ph w
  assert |- ( A e. { <. <. x , y >. , z >. | ph } -> th )

  proof
    cA
    wph
    vx
    vy
    vz
    coprab
    #
    wcel
    #
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    vz
    cv
    #
    cop
    #
    wceq
    #
    wph
    wa
    #
    vz
    wex
    #
    vy
    wex
    #
    vx
    wex
    #
    wth
    @1
    @11
    vw
    cv
    #
    @6
    wceq
    #
    wph
    wa
    #
    vz
    wex
    vy
    wex
    vx
    wex
    @11
    vw
    cA
    @0
    @0
    @12
    cA
    wceq
    #
    @14
    @8
    vx
    vy
    vz
    @15
    @13
    @7
    wph
    @12
    cA
    @6
    eqeq1
    anbi1d
    3exbidv
    wph
    vx
    vy
    vz
    vw
    df-oprab
    elab2g
    ibi
    @10
    wth
    vx
    @9
    wth
    vy
    @8
    wth
    vz
    @7
    wph
    wth
    @7
    wph
    wps
    wch
    wth
    @7
    @2
    cA
    c1st
    cfv
    #
    c1st
    cfv
    #
    wceq
    wph
    wps
    wb
    @7
    @17
    @4
    c1st
    cfv
    @2
    @7
    @16
    @4
    c1st
    @4
    @5
    cA
    @2
    @3
    opex
    #
    vz
    vex
    #
    op1std
    #
    fveq2d
    @2
    @3
    vx
    vex
    #
    vy
    vex
    #
    op1st
    syl6req
    eloprabi.1
    syl
    @7
    @3
    @16
    c2nd
    cfv
    #
    wceq
    wps
    wch
    wb
    @7
    @23
    @4
    c2nd
    cfv
    @3
    @7
    @16
    @4
    c2nd
    @20
    fveq2d
    @2
    @3
    @21
    @22
    op2nd
    syl6req
    eloprabi.2
    syl
    @7
    @5
    cA
    c2nd
    cfv
    #
    wceq
    wch
    wth
    wb
    @7
    @24
    @5
    @4
    @5
    cA
    @18
    @19
    op2ndd
    eqcomd
    eloprabi.3
    syl
    3bitrd
    biimpa
    exlimiv
    exlimiv
    exlimiv
    syl
end
