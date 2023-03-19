include "cvv.mm"
include "wcel.mm"
include "crio.mm"
include "csb.mm"
include "wsbc.mm"
include "wceq.mm"
include "cv.mm"
include "wsb.mm"
include "csbeq1.mm"
include "dfsbcq2.mm"
include "riotabidv.mm"
include "eqeq12d.mm"
include "vex.mm"
include "nfs1v.mm"
include "nfcv.mm"
include "nfriota.mm"
include "weq.mm"
include "sbequ12.mm"
include "csbief.mm"
include "vtoclg.mm"
include "wn.mm"
include "c0.mm"
include "csbprc.mm"
include "wa.mm"
include "cio.mm"
include "df-riota.mm"
include "weu.mm"
include "wex.mm"
include "euex.mm"
include "sbcex.mm"
include "adantl.mm"
include "exlimiv.mm"
include "syl.mm"
include "con3i.mm"
include "iotanul.mm"
include "syl5req.mm"
include "eqtrd.mm"
include "pm2.61i.mm"

theorem csbriota
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z

  disjoint A y
  disjoint B x
  disjoint x y
  disjoint y z
  disjoint A z
  disjoint x z
  disjoint B z
  disjoint ph z
  assert |- [_ A / x ]_ ( iota_ y e. B ph ) = ( iota_ y e. B [. A / x ]. ph )

  proof
    cA
    cvv
    wcel
    #
    vx
    cA
    wph
    vy
    cB
    crio
    #
    csb
    #
    wph
    vx
    cA
    wsbc
    #
    vy
    cB
    crio
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
    cB
    crio
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
    cB
    wph
    vx
    vz
    cA
    dfsbcq2
    riotabidv
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
    cB
    wph
    vx
    vz
    nfs1v
    vx
    cB
    nfcv
    nfriota
    vx
    vz
    weq
    wph
    @8
    vy
    cB
    wph
    vx
    vz
    sbequ12
    riotabidv
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
    @4
    vy
    cv
    cB
    wcel
    #
    @3
    wa
    #
    vy
    cio
    #
    c0
    @3
    vy
    cB
    df-riota
    @11
    @13
    vy
    weu
    #
    wn
    @14
    c0
    wceq
    @15
    @0
    @15
    @13
    vy
    wex
    @0
    @13
    vy
    euex
    @13
    @0
    vy
    @3
    @0
    @12
    wph
    vx
    cA
    sbcex
    adantl
    exlimiv
    syl
    con3i
    @13
    vy
    iotanul
    syl
    syl5req
    eqtrd
    pm2.61i
end
