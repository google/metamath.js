include "cv.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "ccnv.mm"
include "coprab.mm"
include "dfoprab3.mm"
include "cnveqi.mm"
include "cin.mm"
include "cnvopab.mm"
include "inopab.mm"
include "wss.mm"
include "wceq.mm"
include "ssopab2i.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "3eqtr2i.mm"
include "eqtr3i.mm"

theorem cnvoprab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  assume cnvoprab.1: |- ( a = <. x , y >. -> ( ps <-> ph ) )
  assume cnvoprab.2: |- ( ps -> a e. ( _V X. _V ) )

  disjoint a x
  disjoint a y
  disjoint a z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint a ph
  disjoint ps x
  disjoint ps y
  assert |- `' { <. <. x , y >. , z >. | ph } = { <. z , a >. | ps }

  proof
    va
    cv
    cvv
    cvv
    cxp
    wcel
    #
    wps
    wa
    #
    va
    vz
    copab
    #
    ccnv
    #
    wph
    vx
    vy
    vz
    coprab
    #
    ccnv
    wps
    vz
    va
    copab
    #
    @2
    @4
    wps
    wph
    vx
    vy
    vz
    va
    cnvoprab.1
    dfoprab3
    cnveqi
    @3
    @1
    vz
    va
    copab
    @0
    vz
    va
    copab
    #
    @5
    cin
    #
    @5
    @1
    va
    vz
    cnvopab
    @0
    wps
    vz
    va
    inopab
    @5
    @6
    wss
    @7
    @5
    wceq
    wps
    @0
    vz
    va
    cnvoprab.2
    ssopab2i
    @5
    @6
    sseqin2
    mpbi
    3eqtr2i
    eqtr3i
end
