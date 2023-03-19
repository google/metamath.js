include "cvv.mm"
include "wcel.mm"
include "cio.mm"
include "csb.mm"
include "wsbc.mm"
include "wceq.mm"
include "cv.mm"
include "wsb.mm"
include "csbeq1.mm"
include "dfsbcq2.mm"
include "iotabidv.mm"
include "eqeq12d.mm"
include "vex.mm"
include "nfs1v.mm"
include "nfiota.mm"
include "weq.mm"
include "sbequ12.mm"
include "csbief.mm"
include "vtoclg.mm"
include "wn.mm"
include "c0.mm"
include "csbprc.mm"
include "wex.mm"
include "weu.mm"
include "sbcex.mm"
include "con3i.mm"
include "nexdv.mm"
include "euex.mm"
include "iotanul.mm"
include "3syl.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem csbiota
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint A y
  disjoint x y
  disjoint A z
  disjoint y z
  disjoint x z
  disjoint ph z
  assert |- [_ A / x ]_ ( iota y ph ) = ( iota y [. A / x ]. ph )

  proof
    cA
    cvv
    wcel
    #
    vx
    cA
    wph
    vy
    cio
    #
    csb
    #
    wph
    vx
    cA
    wsbc
    #
    vy
    cio
    #
    wceq
    #
    vx
    vz
    cv
    #
    @1
    csb
    #
    wph
    vx
    vz
    wsb
    #
    vy
    cio
    #
    wceq
    @5
    vz
    cA
    cvv
    @6
    cA
    wceq
    #
    @7
    @2
    @9
    @4
    vx
    @6
    cA
    @1
    csbeq1
    @10
    @8
    @3
    vy
    wph
    vx
    vz
    cA
    dfsbcq2
    iotabidv
    eqeq12d
    vx
    @6
    @1
    @9
    vz
    vex
    @8
    vx
    vy
    wph
    vx
    vz
    nfs1v
    nfiota
    vx
    vz
    weq
    wph
    @8
    vy
    wph
    vx
    vz
    sbequ12
    iotabidv
    csbief
    vtoclg
    @0
    wn
    #
    @2
    c0
    @4
    vx
    cA
    @1
    csbprc
    @11
    @3
    vy
    wex
    #
    wn
    @3
    vy
    weu
    #
    wn
    @4
    c0
    wceq
    @11
    @3
    vy
    @3
    @0
    wph
    vx
    cA
    sbcex
    con3i
    nexdv
    @13
    @12
    @3
    vy
    euex
    con3i
    @3
    vy
    iotanul
    3syl
    eqtr4d
    pm2.61i
end
