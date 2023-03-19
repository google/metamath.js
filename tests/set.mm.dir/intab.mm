include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cab.mm"
include "cint.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wss.mm"
include "cvv.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "cbvabv.mm"
include "eqeltri.mm"
include "nfe1.mm"
include "nfab.mm"
include "nfeq2.mm"
include "eleq2.mm"
include "imbi2d.mm"
include "albid.mm"
include "elab.mm"
include "wsbc.mm"
include "19.8a.mm"
include "ex.mm"
include "alrimiv.mm"
include "sbc6.mm"
include "sylibr.mm"
include "df-sbc.mm"
include "sylib.mm"
include "mpgbir.mm"
include "intss1.mm"
include "ax-mp.mm"
include "19.29r.mm"
include "simplr.mm"
include "pm3.35.mm"
include "adantlr.mm"
include "eqeltrd.mm"
include "exlimiv.mm"
include "syl.mm"
include "vex.mm"
include "elintab.mm"
include "abssi.mm"
include "eqssi.mm"
include "eqtri.mm"

theorem intab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume intab.1: |- A e. _V
  assume intab.2: |- { x | E. y ( ph /\ x = A ) } e. _V

  disjoint A x
  disjoint ph x
  disjoint x y
  disjoint x z
  disjoint A z
  disjoint ph z
  disjoint y z
  assert |- |^| { x | A. y ( ph -> A e. x ) } = { x | E. y ( ph /\ x = A ) }

  proof
    wph
    cA
    vx
    cv
    #
    wcel
    #
    wi
    #
    vy
    wal
    #
    vx
    cab
    #
    cint
    #
    wph
    vz
    cv
    #
    cA
    wceq
    #
    wa
    #
    vy
    wex
    #
    vz
    cab
    #
    wph
    @0
    cA
    wceq
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    @5
    @10
    @10
    @4
    wcel
    #
    @5
    @10
    wss
    @15
    wph
    cA
    @10
    wcel
    #
    wi
    #
    vy
    @3
    @17
    vy
    wal
    vx
    @10
    @10
    @14
    cvv
    @9
    @13
    vz
    vx
    @6
    @0
    wceq
    #
    @8
    @12
    vy
    @18
    @7
    @11
    wph
    @6
    @0
    cA
    eqeq1
    anbi2d
    exbidv
    cbvabv
    #
    intab.2
    eqeltri
    @0
    @10
    wceq
    #
    @2
    @17
    vy
    vy
    @0
    @10
    @9
    vy
    vz
    @8
    vy
    nfe1
    nfab
    nfeq2
    @20
    @1
    @16
    wph
    @0
    @10
    cA
    eleq2
    imbi2d
    albid
    elab
    wph
    @9
    vz
    cA
    wsbc
    #
    @16
    wph
    @7
    @9
    wi
    #
    vz
    wal
    @21
    wph
    @22
    vz
    wph
    @7
    @9
    @8
    vy
    19.8a
    ex
    alrimiv
    @9
    vz
    cA
    intab.1
    sbc6
    sylibr
    @9
    vz
    cA
    df-sbc
    sylib
    mpgbir
    @10
    @4
    intss1
    ax-mp
    @9
    vz
    @5
    @9
    @3
    @6
    @0
    wcel
    #
    wi
    #
    vx
    wal
    @6
    @5
    wcel
    @9
    @24
    vx
    @9
    @3
    @23
    @9
    @3
    wa
    @8
    @2
    wa
    #
    vy
    wex
    @23
    @8
    @2
    vy
    19.29r
    @25
    @23
    vy
    @25
    @6
    cA
    @0
    wph
    @7
    @2
    simplr
    wph
    @2
    @1
    @7
    wph
    @1
    pm3.35
    adantlr
    eqeltrd
    exlimiv
    syl
    ex
    alrimiv
    @3
    vx
    @6
    vz
    vex
    elintab
    sylibr
    abssi
    eqssi
    @19
    eqtri
end
