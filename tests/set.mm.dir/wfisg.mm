include "wwe.mm"
include "wse.mm"
include "wa.mm"
include "crab.mm"
include "wceq.mm"
include "wral.mm"
include "wss.mm"
include "cv.mm"
include "cpred.mm"
include "wcel.mm"
include "wi.mm"
include "ssrab2.mm"
include "wsbc.mm"
include "dfss3.mm"
include "nfcv.mm"
include "elrabsf.mm"
include "simprbi.mm"
include "ralimi.mm"
include "sylbi.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "nfral.mm"
include "nfim.mm"
include "eleq1.mm"
include "predeq3.mm"
include "raleqdv.mm"
include "sbceq1a.mm"
include "imbi12d.mm"
include "chvar.mm"
include "syl5.mm"
include "anc2li.mm"
include "syl6ibr.mm"
include "rgen.mm"
include "wfi.mm"
include "mpanr12.mm"
include "rabid2.mm"
include "sylib.mm"

theorem wfisg
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  let vw: setvar w
  assume wfisg.1: |- ( y e. A -> ( A. z e. Pred ( R , A , y ) [. z / y ]. ph -> ph ) )

  disjoint A y
  disjoint A z
  disjoint ph z
  disjoint R y
  disjoint R z
  disjoint y z
  disjoint A w
  disjoint w y
  disjoint ph w
  disjoint R w
  disjoint w z
  assert |- ( ( R We A /\ R Se A ) -> A. y e. A ph )

  proof
    cA
    cR
    wwe
    cA
    cR
    wse
    wa
    #
    cA
    wph
    vy
    cA
    crab
    #
    wceq
    #
    wph
    vy
    cA
    wral
    @0
    @1
    cA
    wss
    cA
    cR
    vw
    cv
    #
    cpred
    #
    @1
    wss
    #
    @3
    @1
    wcel
    #
    wi
    #
    vw
    cA
    wral
    @2
    wph
    vy
    cA
    ssrab2
    @7
    vw
    cA
    @3
    cA
    wcel
    #
    @5
    @8
    wph
    vy
    @3
    wsbc
    #
    wa
    @6
    @8
    @5
    @9
    @5
    wph
    vy
    vz
    cv
    #
    wsbc
    #
    vz
    @4
    wral
    #
    @8
    @9
    @5
    @10
    @1
    wcel
    #
    vz
    @4
    wral
    @12
    vz
    @4
    @1
    dfss3
    @13
    @11
    vz
    @4
    @13
    @10
    cA
    wcel
    @11
    wph
    vy
    @10
    cA
    vy
    cA
    nfcv
    #
    elrabsf
    simprbi
    ralimi
    sylbi
    vy
    cv
    #
    cA
    wcel
    #
    @11
    vz
    cA
    cR
    @15
    cpred
    #
    wral
    #
    wph
    wi
    #
    wi
    @8
    @12
    @9
    wi
    #
    wi
    vy
    vw
    @8
    @20
    vy
    @8
    vy
    nfv
    @12
    @9
    vy
    @11
    vy
    vz
    @4
    vy
    @4
    nfcv
    wph
    vy
    @10
    nfsbc1v
    nfral
    wph
    vy
    @3
    nfsbc1v
    nfim
    nfim
    @15
    @3
    wceq
    #
    @16
    @8
    @19
    @20
    @15
    @3
    cA
    eleq1
    @21
    @18
    @12
    wph
    @9
    @21
    @11
    vz
    @17
    @4
    cA
    cR
    @15
    @3
    predeq3
    raleqdv
    wph
    vy
    @3
    sbceq1a
    imbi12d
    imbi12d
    wfisg.1
    chvar
    syl5
    anc2li
    wph
    vy
    @3
    cA
    @14
    elrabsf
    syl6ibr
    rgen
    vw
    cA
    @1
    cR
    wfi
    mpanr12
    wph
    vy
    cA
    rabid2
    sylib
end
