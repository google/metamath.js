include "cif.mm"
include "crab.mm"
include "wn.mm"
include "cun.mm"
include "cin.mm"
include "cvv.mm"
include "cdif.mm"
include "dfif6.mm"
include "cab.mm"
include "weq.mm"
include "biidd.mm"
include "cbvabv.mm"
include "eqtri.mm"
include "ineq2i.mm"
include "dfrab3.mm"
include "eqtr4i.mm"
include "notab.mm"
include "difeq2i.mm"
include "eqtr2i.mm"
include "uneq12i.mm"

theorem dfif3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume dfif3.1: |- C = { x | ph }

  disjoint ph x
  disjoint A y
  disjoint B y
  disjoint x y
  disjoint ph y
  assert |- if ( ph , A , B ) = ( ( A i^i C ) u. ( B i^i ( _V \ C ) ) )

  proof
    wph
    cA
    cB
    cif
    wph
    vy
    cA
    crab
    #
    wph
    wn
    #
    vy
    cB
    crab
    #
    cun
    cA
    cC
    cin
    #
    cB
    cvv
    cC
    cdif
    #
    cin
    #
    cun
    wph
    vy
    cA
    cB
    dfif6
    @3
    @0
    @5
    @2
    @3
    cA
    wph
    vy
    cab
    #
    cin
    @0
    cC
    @6
    cA
    cC
    wph
    vx
    cab
    @6
    dfif3.1
    wph
    wph
    vx
    vy
    vx
    vy
    weq
    wph
    biidd
    cbvabv
    eqtri
    #
    ineq2i
    wph
    vy
    cA
    dfrab3
    eqtr4i
    @2
    cB
    @1
    vy
    cab
    #
    cin
    @5
    @1
    vy
    cB
    dfrab3
    @8
    @4
    cB
    @8
    cvv
    @6
    cdif
    @4
    wph
    vy
    notab
    cC
    @6
    cvv
    @7
    difeq2i
    eqtr4i
    ineq2i
    eqtr2i
    uneq12i
    eqtr4i
end
