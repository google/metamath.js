include "cv.mm"
include "cfv.mm"
include "cio.mm"
include "wceq.mm"
include "cdm.mm"
include "fveq2.mm"
include "iotabidv.mm"
include "eqeq12d.mm"
include "wcel.mm"
include "wbr.mm"
include "wex.mm"
include "vex.mm"
include "eldm.mm"
include "nfiota1.mm"
include "nfeq2.mm"
include "wfun.mm"
include "wi.mm"
include "opabiotafun.mm"
include "funbrfv.mm"
include "ax-mp.mm"
include "cab.mm"
include "csn.mm"
include "cop.mm"
include "copab.mm"
include "df-br.mm"
include "eleq2i.mm"
include "opabid.mm"
include "3bitri.mm"
include "vsnid.mm"
include "id.mm"
include "syl5eleqr.mm"
include "abid.mm"
include "sylib.mm"
include "sylbi.mm"
include "weu.mm"
include "wb.mm"
include "breldm.mm"
include "opabiotadm.mm"
include "abeq2i.mm"
include "iota1.mm"
include "syl.mm"
include "mpbid.mm"
include "eqtr4d.mm"
include "exlimi.mm"
include "vtoclga.mm"

theorem opabiota
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cF: class F
  let vz: setvar z
  assume opabiota.1: |- F = { <. x , y >. | { y | ph } = { y } }
  assume opabiota.2: |- ( x = B -> ( ph <-> ps ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint ps x
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint F z
  disjoint ph z
  disjoint ps z
  assert |- ( B e. dom F -> ( F ` B ) = ( iota y ps ) )

  proof
    vx
    cv
    #
    cF
    cfv
    #
    wph
    vy
    cio
    #
    wceq
    #
    cB
    cF
    cfv
    #
    wps
    vy
    cio
    #
    wceq
    vx
    cB
    cF
    cdm
    #
    @0
    cB
    wceq
    #
    @1
    @4
    @2
    @5
    @0
    cB
    cF
    fveq2
    @7
    wph
    wps
    vy
    opabiota.2
    iotabidv
    eqeq12d
    @0
    @6
    wcel
    #
    @0
    vy
    cv
    #
    cF
    wbr
    #
    vy
    wex
    @3
    vy
    @0
    cF
    vx
    vex
    #
    eldm
    @10
    @3
    vy
    vy
    @1
    @2
    wph
    vy
    nfiota1
    nfeq2
    @10
    @1
    @9
    @2
    cF
    wfun
    @10
    @1
    @9
    wceq
    wi
    wph
    vx
    vy
    cF
    opabiota.1
    opabiotafun
    @0
    @9
    cF
    funbrfv
    ax-mp
    @10
    wph
    @2
    @9
    wceq
    #
    @10
    wph
    vy
    cab
    #
    @9
    csn
    #
    wceq
    #
    wph
    @10
    @0
    @9
    cop
    #
    cF
    wcel
    @16
    @15
    vx
    vy
    copab
    #
    wcel
    @15
    @0
    @9
    cF
    df-br
    cF
    @17
    @16
    opabiota.1
    eleq2i
    @15
    vx
    vy
    opabid
    3bitri
    @15
    @9
    @13
    wcel
    wph
    @15
    @9
    @14
    @13
    vy
    vsnid
    @15
    id
    syl5eleqr
    wph
    vy
    abid
    sylib
    sylbi
    @10
    wph
    vy
    weu
    #
    wph
    @12
    wb
    @10
    @8
    @18
    @0
    @9
    cF
    @11
    vy
    vex
    breldm
    @18
    vx
    @6
    wph
    vx
    vy
    cF
    opabiota.1
    opabiotadm
    abeq2i
    sylib
    wph
    vy
    iota1
    syl
    mpbid
    eqtr4d
    exlimi
    sylbi
    vtoclga
end
