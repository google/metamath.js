include "wcel.mm"
include "wreu.mm"
include "crio.mm"
include "riotacl.mm"
include "wn.mm"
include "cund.mm"
include "cfv.mm"
include "undefnel2.mm"
include "cv.mm"
include "wa.mm"
include "cio.mm"
include "cab.mm"
include "cif.mm"
include "iffalse.mm"
include "ax-riotaBAD.mm"
include "abid1.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "eleq1d.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "con4d.mm"
include "impbid2.mm"

theorem riotaclbgBAD
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V

  disjoint A x
  assert |- ( A e. V -> ( E! x e. A ph <-> ( iota_ x e. A ph ) e. A ) )

  proof
    cA
    cV
    wcel
    #
    wph
    vx
    cA
    wreu
    #
    wph
    vx
    cA
    crio
    #
    cA
    wcel
    #
    wph
    vx
    cA
    riotacl
    @0
    @1
    @3
    @0
    @3
    wn
    @1
    wn
    #
    cA
    cund
    cfv
    #
    cA
    wcel
    #
    wn
    cA
    cV
    undefnel2
    @4
    @3
    @6
    @4
    @2
    @5
    cA
    @4
    @1
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    vx
    cio
    #
    @7
    vx
    cab
    #
    cund
    cfv
    #
    cif
    @10
    @2
    @5
    @1
    @8
    @10
    iffalse
    wph
    vx
    cA
    ax-riotaBAD
    cA
    @9
    cund
    vx
    cA
    abid1
    fveq2i
    3eqtr4g
    eleq1d
    notbid
    syl5ibrcom
    con4d
    impbid2
end
