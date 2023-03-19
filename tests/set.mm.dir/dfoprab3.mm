include "coprab.mm"
include "cv.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "c2nd.mm"
include "cfv.mm"
include "wsbc.mm"
include "c1st.mm"
include "wa.mm"
include "copab.mm"
include "dfoprab3s.mm"
include "fvex.mm"
include "wceq.mm"
include "wb.mm"
include "cop.mm"
include "eqcom.mm"
include "anbi12i.mm"
include "eqopi.mm"
include "sylan2b.mm"
include "syl.mm"
include "bicomd.mm"
include "ex.mm"
include "sbc2iedv.mm"
include "pm5.32i.mm"
include "opabbii.mm"
include "eqtr2i.mm"

theorem dfoprab3
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume dfoprab3.1: |- ( w = <. x , y >. -> ( ph <-> ps ) )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint ps w
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  assert |- { <. w , z >. | ( w e. ( _V X. _V ) /\ ph ) } = { <. <. x , y >. , z >. | ps }

  proof
    wps
    vx
    vy
    vz
    coprab
    vw
    cv
    #
    cvv
    cvv
    cxp
    wcel
    #
    wps
    vy
    @0
    c2nd
    cfv
    #
    wsbc
    vx
    @0
    c1st
    cfv
    #
    wsbc
    #
    wa
    #
    vw
    vz
    copab
    @1
    wph
    wa
    #
    vw
    vz
    copab
    wps
    vx
    vy
    vz
    vw
    dfoprab3s
    @5
    @6
    vw
    vz
    @1
    @4
    wph
    @1
    wps
    wph
    vx
    vy
    @3
    @2
    @0
    c1st
    fvex
    @0
    c2nd
    fvex
    @1
    vx
    cv
    #
    @3
    wceq
    #
    vy
    cv
    #
    @2
    wceq
    #
    wa
    #
    wps
    wph
    wb
    @1
    @11
    wa
    #
    wph
    wps
    @12
    @0
    @7
    @9
    cop
    wceq
    #
    wph
    wps
    wb
    @11
    @1
    @3
    @7
    wceq
    #
    @2
    @9
    wceq
    #
    wa
    @13
    @8
    @14
    @10
    @15
    @7
    @3
    eqcom
    @9
    @2
    eqcom
    anbi12i
    @0
    @7
    @9
    cvv
    cvv
    eqopi
    sylan2b
    dfoprab3.1
    syl
    bicomd
    ex
    sbc2iedv
    pm5.32i
    opabbii
    eqtr2i
end
