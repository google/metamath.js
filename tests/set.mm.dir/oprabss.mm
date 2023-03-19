include "coprab.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cvv.mm"
include "wrel.mm"
include "wss.mm"
include "reloprab.mm"
include "relssdmrn.mm"
include "ax-mp.mm"
include "reldmoprab.mm"
include "df-rel.mm"
include "mpbi.mm"
include "ssv.mm"
include "xpss12.mm"
include "mp2an.mm"
include "sstri.mm"

theorem oprabss
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- { <. <. x , y >. , z >. | ph } C_ ( ( _V X. _V ) X. _V )

  proof
    wph
    vx
    vy
    vz
    coprab
    #
    @0
    cdm
    #
    @0
    crn
    #
    cxp
    #
    cvv
    cvv
    cxp
    #
    cvv
    cxp
    #
    @0
    wrel
    @0
    @3
    wss
    wph
    vx
    vy
    vz
    reloprab
    @0
    relssdmrn
    ax-mp
    @1
    @4
    wss
    #
    @2
    cvv
    wss
    @3
    @5
    wss
    @1
    wrel
    @6
    wph
    vx
    vy
    vz
    reldmoprab
    @1
    df-rel
    mpbi
    @2
    ssv
    @1
    @4
    @2
    cvv
    xpss12
    mp2an
    sstri
end
