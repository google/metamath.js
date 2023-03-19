include "cv.mm"
include "wtr.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "wss.mm"
include "wi.mm"
include "setindtr.mm"
include "wral.mm"
include "dfss3.mm"
include "nfcv.mm"
include "nfsab1.mm"
include "nfral.mm"
include "nfim.mm"
include "weq.mm"
include "raleq.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "vex.mm"
include "elab.mm"
include "ralbii.mm"
include "abid.mm"
include "3imtr4i.mm"
include "chvar.mm"
include "sylbi.mm"
include "mpg.mm"
include "cvv.mm"
include "wb.mm"
include "elex.mm"
include "adantl.mm"
include "exlimiv.mm"
include "elabg.mm"
include "syl.mm"
include "mpbid.mm"

theorem setindtrs
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let va: setvar a
  assume setindtrs.a: |- ( A. y e. x ps -> ph )
  assume setindtrs.b: |- ( x = y -> ( ph <-> ps ) )
  assume setindtrs.c: |- ( x = B -> ( ph <-> ch ) )

  disjoint B x
  disjoint B z
  disjoint x z
  disjoint ph y
  disjoint ps x
  disjoint ch x
  disjoint ph z
  disjoint x y
  disjoint B a
  disjoint a x
  disjoint a z
  disjoint a ph
  disjoint a y
  assert |- ( E. z ( Tr z /\ B e. z ) -> ch )

  proof
    vz
    cv
    #
    wtr
    #
    cB
    @0
    wcel
    #
    wa
    #
    vz
    wex
    #
    cB
    wph
    vx
    cab
    #
    wcel
    #
    wch
    va
    cv
    #
    @5
    wss
    #
    @7
    @5
    wcel
    #
    wi
    @4
    @6
    wi
    va
    va
    vz
    @5
    cB
    setindtr
    @8
    vy
    cv
    #
    @5
    wcel
    #
    vy
    @7
    wral
    #
    @9
    vy
    @7
    @5
    dfss3
    @11
    vy
    vx
    cv
    #
    wral
    #
    @13
    @5
    wcel
    #
    wi
    @12
    @9
    wi
    vx
    va
    @12
    @9
    vx
    @11
    vx
    vy
    @7
    vx
    @7
    nfcv
    wph
    vx
    vy
    nfsab1
    nfral
    wph
    vx
    va
    nfsab1
    nfim
    vx
    va
    weq
    @14
    @12
    @15
    @9
    @11
    vy
    @13
    @7
    raleq
    @13
    @7
    @5
    eleq1
    imbi12d
    wps
    vy
    @13
    wral
    wph
    @14
    @15
    setindtrs.a
    @11
    wps
    vy
    @13
    wph
    wps
    vx
    @10
    vy
    vex
    setindtrs.b
    elab
    ralbii
    wph
    vx
    abid
    3imtr4i
    chvar
    sylbi
    mpg
    @4
    cB
    cvv
    wcel
    #
    @6
    wch
    wb
    @3
    @16
    vz
    @2
    @16
    @1
    cB
    @0
    elex
    adantl
    exlimiv
    wph
    wch
    vx
    cB
    cvv
    setindtrs.c
    elabg
    syl
    mpbid
end
