include "cv.mm"
include "con0.mm"
include "wcel.mm"
include "crab.mm"
include "wss.mm"
include "wi.mm"
include "wral.mm"
include "wceq.mm"
include "ssrab2.mm"
include "wa.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfss.mm"
include "nfcri.mm"
include "nfim.mm"
include "dfss3.mm"
include "sseq1.mm"
include "syl5bbr.mm"
include "rabid.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "wsb.mm"
include "sbequ.mm"
include "nfv.mm"
include "nfs1v.mm"
include "sbequ12.mm"
include "cbvrab.mm"
include "elrab2.mm"
include "simprbi.mm"
include "ralimi.mm"
include "syl5.mm"
include "anc2li.mm"
include "vtoclgaf.mm"
include "rgen.mm"
include "tfi.mm"
include "mp2an.mm"
include "eqcomi.mm"
include "rabeq2i.mm"

theorem tfis
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  assume tfis.1: |- ( x e. On -> ( A. y e. x [ y / x ] ph -> ph ) )

  disjoint ph y
  disjoint x y
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint y z
  disjoint ph z
  disjoint w x
  disjoint x z
  assert |- ( x e. On -> ph )

  proof
    vx
    cv
    #
    con0
    wcel
    #
    @1
    wph
    wph
    vx
    con0
    con0
    wph
    vx
    con0
    crab
    #
    con0
    @2
    con0
    wss
    vz
    cv
    #
    @2
    wss
    #
    @3
    @2
    wcel
    #
    wi
    #
    vz
    con0
    wral
    @2
    con0
    wceq
    wph
    vx
    con0
    ssrab2
    @6
    vz
    con0
    vy
    cv
    #
    @2
    wcel
    #
    vy
    @0
    wral
    #
    @1
    wph
    wa
    #
    wi
    @6
    vx
    @3
    con0
    vx
    @3
    nfcv
    #
    @4
    @5
    vx
    vx
    @3
    @2
    @11
    wph
    vx
    con0
    nfrab1
    #
    nfss
    vx
    vz
    @2
    @12
    nfcri
    nfim
    @0
    @3
    wceq
    #
    @9
    @4
    @10
    @5
    @9
    @0
    @2
    wss
    @13
    @4
    vy
    @0
    @2
    dfss3
    @0
    @3
    @2
    sseq1
    syl5bbr
    @10
    @0
    @2
    wcel
    @13
    @5
    wph
    vx
    con0
    rabid
    @0
    @3
    @2
    eleq1
    syl5bbr
    imbi12d
    @1
    @9
    wph
    @9
    wph
    vx
    vy
    wsb
    #
    vy
    @0
    wral
    @1
    wph
    @8
    @14
    vy
    @0
    @8
    @7
    con0
    wcel
    @14
    wph
    vx
    vw
    wsb
    #
    @14
    vw
    @7
    con0
    @2
    wph
    vw
    vy
    vx
    sbequ
    wph
    @15
    vx
    vw
    con0
    vx
    con0
    nfcv
    vw
    con0
    nfcv
    wph
    vw
    nfv
    wph
    vx
    vw
    nfs1v
    wph
    vx
    vw
    sbequ12
    cbvrab
    elrab2
    simprbi
    ralimi
    tfis.1
    syl5
    anc2li
    vtoclgaf
    rgen
    vz
    @2
    tfi
    mp2an
    eqcomi
    rabeq2i
    simprbi
end
