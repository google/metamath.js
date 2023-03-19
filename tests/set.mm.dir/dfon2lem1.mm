include "cv.mm"
include "wtr.mm"
include "w3a.mm"
include "cab.mm"
include "cuni.mm"
include "truni.mm"
include "wcel.mm"
include "wsbc.mm"
include "nfsbc1v.mm"
include "nfv.mm"
include "nf3an.mm"
include "vex.mm"
include "weq.mm"
include "sbceq1a.mm"
include "treq.mm"
include "3anbi123d.mm"
include "elabf.mm"
include "simp2bi.mm"
include "mprg.mm"

theorem dfon2lem1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- Tr U. { x | ( ph /\ Tr x /\ ps ) }

  proof
    vy
    cv
    #
    wtr
    #
    wph
    vx
    cv
    #
    wtr
    #
    wps
    w3a
    #
    vx
    cab
    #
    cuni
    wtr
    vy
    @5
    vy
    @5
    truni
    @0
    @5
    wcel
    wph
    vx
    @0
    wsbc
    #
    @1
    wps
    vx
    @0
    wsbc
    #
    @4
    @6
    @1
    @7
    w3a
    vx
    @0
    @6
    @1
    @7
    vx
    wph
    vx
    @0
    nfsbc1v
    @1
    vx
    nfv
    wps
    vx
    @0
    nfsbc1v
    nf3an
    vy
    vex
    vx
    vy
    weq
    wph
    @6
    @3
    @1
    wps
    @7
    wph
    vx
    @0
    sbceq1a
    @2
    @0
    treq
    wps
    vx
    @0
    sbceq1a
    3anbi123d
    elabf
    simp2bi
    mprg
end
