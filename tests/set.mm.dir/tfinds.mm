include "cv.mm"
include "con0.mm"
include "wcel.mm"
include "wlim.mm"
include "wral.mm"
include "wi.mm"
include "wn.mm"
include "word.mm"
include "c0.mm"
include "wceq.mm"
include "csuc.mm"
include "wrex.mm"
include "wo.mm"
include "wa.mm"
include "dflim3.mm"
include "notbii.mm"
include "iman.mm"
include "eloni.mm"
include "pm2.27.mm"
include "syl.mm"
include "mpbiri.mm"
include "a1d.mm"
include "nfra1.mm"
include "nfv.mm"
include "nfim.mm"
include "vex.mm"
include "sucid.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "syl5.mm"
include "wsb.mm"
include "raleq.mm"
include "sbie.mm"
include "sbequ.mm"
include "syl5bbr.mm"
include "cbvralv.mm"
include "cbvralsv.mm"
include "3bitr4g.mm"
include "imbi1d.mm"
include "syl5ibrcom.mm"
include "biimprd.mm"
include "a1i.mm"
include "syldd.mm"
include "rexlimi.mm"
include "jaoi.mm"
include "syl6.mm"
include "syl5bir.mm"
include "syl5bi.mm"
include "pm2.61d2.mm"
include "tfis3.mm"

theorem tfinds
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume tfinds.1: |- ( x = (/) -> ( ph <-> ps ) )
  assume tfinds.2: |- ( x = y -> ( ph <-> ch ) )
  assume tfinds.3: |- ( x = suc y -> ( ph <-> th ) )
  assume tfinds.4: |- ( x = A -> ( ph <-> ta ) )
  assume tfinds.5: |- ps
  assume tfinds.6: |- ( y e. On -> ( ch -> th ) )
  assume tfinds.7: |- ( Lim x -> ( A. y e. x ch -> ph ) )

  disjoint x y
  disjoint A x
  disjoint ch x
  disjoint ta x
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint ch z
  disjoint ph z
  assert |- ( A e. On -> ta )

  proof
    wph
    wch
    wta
    vx
    vy
    cA
    tfinds.2
    tfinds.4
    vx
    cv
    #
    con0
    wcel
    #
    @0
    wlim
    #
    wch
    vy
    @0
    wral
    #
    wph
    wi
    #
    @2
    wn
    @0
    word
    #
    @0
    c0
    wceq
    #
    @0
    vy
    cv
    #
    csuc
    #
    wceq
    #
    vy
    con0
    wrex
    #
    wo
    #
    wn
    wa
    #
    wn
    #
    @1
    @4
    @2
    @12
    vy
    @0
    dflim3
    notbii
    @13
    @5
    @11
    wi
    #
    @1
    @4
    @5
    @11
    iman
    @1
    @14
    @11
    @4
    @1
    @5
    @14
    @11
    wi
    @0
    eloni
    @5
    @11
    pm2.27
    syl
    @6
    @4
    @10
    @6
    wph
    @3
    @6
    wph
    wps
    tfinds.5
    tfinds.1
    mpbiri
    a1d
    @9
    @4
    vy
    con0
    @3
    wph
    vy
    wch
    vy
    @0
    nfra1
    wph
    vy
    nfv
    nfim
    @7
    con0
    wcel
    #
    @9
    @3
    wth
    wph
    @15
    @3
    wth
    wi
    @9
    wph
    vx
    @8
    wral
    #
    wth
    wi
    @16
    wch
    @15
    wth
    @7
    @8
    wcel
    @16
    wch
    wi
    @7
    vy
    vex
    sucid
    wph
    wch
    vx
    @7
    @8
    tfinds.2
    rspcv
    ax-mp
    tfinds.6
    syl5
    @9
    @3
    @16
    wth
    @9
    wph
    vx
    vz
    wsb
    #
    vz
    @0
    wral
    @17
    vz
    @8
    wral
    @3
    @16
    @17
    vz
    @0
    @8
    raleq
    wch
    @17
    vy
    vz
    @0
    wch
    wph
    vx
    vy
    wsb
    @7
    vz
    cv
    wceq
    @17
    wph
    wch
    vx
    vy
    wch
    vx
    nfv
    tfinds.2
    sbie
    wph
    vy
    vz
    vx
    sbequ
    syl5bbr
    cbvralv
    wph
    vx
    vz
    @8
    cbvralsv
    3bitr4g
    imbi1d
    syl5ibrcom
    @9
    wth
    wph
    wi
    wi
    @15
    @9
    wph
    wth
    tfinds.3
    biimprd
    a1i
    syldd
    rexlimi
    jaoi
    syl6
    syl5bir
    syl5bi
    tfinds.7
    pm2.61d2
    tfis3
end
