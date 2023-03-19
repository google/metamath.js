include "c0.mm"
include "wne.mm"
include "wwe.mm"
include "wcel.mm"
include "wsbc.mm"
include "wex.mm"
include "19.8a.mm"
include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "cab.mm"
include "scott0s.mm"
include "neeq1i.mm"
include "bitr4i.mm"
include "sylib.mm"
include "cvv.mm"
include "scottexs.mm"
include "eqeltri.mm"
include "htalem.mm"
include "ex.mm"
include "simpl.mm"
include "ss2abi.mm"
include "eqsstri.mm"
include "sseli.mm"
include "df-sbc.mm"
include "sylibr.mm"
include "syl56.mm"

theorem hta
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  assume hta.1: |- A = { x | ( ph /\ A. y ( [. y / x ]. ph -> ( rank ` x ) C_ ( rank ` y ) ) ) }
  assume hta.2: |- B = ( iota_ z e. A A. w e. A -. w R z )

  disjoint x y
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint ph y
  disjoint R w
  disjoint R z
  assert |- ( R We A -> ( ph -> [. B / x ]. ph ) )

  proof
    wph
    cA
    c0
    wne
    #
    cA
    cR
    wwe
    #
    cB
    cA
    wcel
    #
    wph
    vx
    cB
    wsbc
    #
    wph
    wph
    vx
    wex
    #
    @0
    wph
    vx
    19.8a
    @4
    wph
    wph
    vx
    vy
    cv
    #
    wsbc
    vx
    cv
    crnk
    cfv
    @5
    crnk
    cfv
    wss
    wi
    vy
    wal
    #
    wa
    #
    vx
    cab
    #
    c0
    wne
    @0
    wph
    vx
    vy
    scott0s
    cA
    @8
    c0
    hta.1
    neeq1i
    bitr4i
    sylib
    @1
    @0
    @2
    vz
    vw
    cA
    cB
    cR
    cA
    @8
    cvv
    hta.1
    wph
    vx
    vy
    scottexs
    eqeltri
    hta.2
    htalem
    ex
    @2
    cB
    wph
    vx
    cab
    #
    wcel
    @3
    cA
    @9
    cB
    cA
    @8
    @9
    hta.1
    @7
    wph
    vx
    wph
    @6
    simpl
    ss2abi
    eqsstri
    sseli
    wph
    vx
    cB
    df-sbc
    sylibr
    syl56
end
