include "wex.mm"
include "wal.mm"
include "nfv.mm"
include "nfe1.mm"
include "wa.mm"
include "cv.mm"
include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "a1i.mm"
include "simpr.mm"
include "spsbcd.mm"
include "sbcid.mm"
include "sylib.mm"
include "sylibr.mm"
include "spesbcd.mm"
include "exlimdd.mm"
include "alrimiv.mm"

theorem ex-natded9.26
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume ex-natded9.26.1: |- ( ph -> E. x A. y ps )

  disjoint x y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> A. y E. x ps )

  proof
    wph
    wps
    vx
    wex
    #
    vy
    wph
    wps
    vy
    wal
    #
    @0
    vx
    wph
    vx
    nfv
    wps
    vx
    nfe1
    ex-natded9.26.1
    wph
    @1
    wa
    #
    wps
    vx
    vx
    cv
    #
    @2
    wps
    wps
    vx
    @3
    wsbc
    @2
    wps
    vy
    vy
    cv
    #
    wsbc
    wps
    @2
    wps
    vy
    @4
    cvv
    @4
    cvv
    wcel
    @2
    vy
    vex
    a1i
    wph
    @1
    simpr
    spsbcd
    wps
    vy
    sbcid
    sylib
    wps
    vx
    sbcid
    sylibr
    spesbcd
    exlimdd
    alrimiv
end
