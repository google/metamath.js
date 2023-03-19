include "coprab.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "c2nd.mm"
include "cfv.mm"
include "wsbc.mm"
include "c1st.mm"
include "dfoprab2.mm"
include "nfsbc1v.mm"
include "19.41.mm"
include "sbcopeq1a.mm"
include "pm5.32i.mm"
include "exbii.mm"
include "nfcv.mm"
include "nfsbc.mm"
include "bitr3i.mm"
include "elvv.mm"
include "anbi1i.mm"
include "3bitr4i.mm"
include "opabbii.mm"
include "eqtri.mm"

theorem dfoprab3s
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint ph w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  assert |- { <. <. x , y >. , z >. | ph } = { <. w , z >. | ( w e. ( _V X. _V ) /\ [. ( 1st ` w ) / x ]. [. ( 2nd ` w ) / y ]. ph ) }

  proof
    wph
    vx
    vy
    vz
    coprab
    vw
    cv
    #
    vx
    cv
    vy
    cv
    cop
    wceq
    #
    wph
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    vw
    vz
    copab
    @0
    cvv
    cvv
    cxp
    wcel
    #
    wph
    vy
    @0
    c2nd
    cfv
    #
    wsbc
    #
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
    wph
    vx
    vy
    vz
    vw
    dfoprab2
    @4
    @10
    vw
    vz
    @1
    vy
    wex
    #
    @9
    wa
    #
    vx
    wex
    @11
    vx
    wex
    #
    @9
    wa
    @4
    @10
    @11
    @9
    vx
    @7
    vx
    @8
    nfsbc1v
    19.41
    @3
    @12
    vx
    @3
    @1
    @9
    wa
    #
    vy
    wex
    @12
    @14
    @2
    vy
    @1
    @9
    wph
    wph
    vx
    vy
    @0
    sbcopeq1a
    pm5.32i
    exbii
    @1
    @9
    vy
    @7
    vy
    vx
    @8
    vy
    @8
    nfcv
    wph
    vy
    @6
    nfsbc1v
    nfsbc
    19.41
    bitr3i
    exbii
    @5
    @13
    @9
    vx
    vy
    @0
    elvv
    anbi1i
    3bitr4i
    opabbii
    eqtri
end
