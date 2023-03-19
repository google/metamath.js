include "copab.mm"
include "cima.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cres.mm"
include "resima.mm"
include "resopab.mm"
include "imaeq1i.mm"
include "eqtr3i.mm"
include "wfun.mm"
include "wmo.mm"
include "funopab.mm"
include "wi.mm"
include "wsb.mm"
include "weq.mm"
include "wal.mm"
include "rspec.mm"
include "nfv.mm"
include "mo3.mm"
include "sylibr.mm"
include "moanimv.mm"
include "mpbir.mm"
include "mpgbir.mm"
include "funimaex.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "isseti.mm"

theorem isarep2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  assume isarep2.1: |- A e. _V
  assume isarep2.2: |- A. x e. A A. y A. z ( ( ph /\ [ z / y ] ph ) -> y = z )

  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint y z
  disjoint ph w
  disjoint ph z
  assert |- E. w w = ( { <. x , y >. | ph } " A )

  proof
    vw
    wph
    vx
    vy
    copab
    #
    cA
    cima
    #
    @1
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    vy
    copab
    #
    cA
    cima
    #
    cvv
    @0
    cA
    cres
    #
    cA
    cima
    @1
    @5
    @0
    cA
    resima
    @6
    @4
    cA
    wph
    vx
    vy
    cA
    resopab
    imaeq1i
    eqtr3i
    @4
    wfun
    #
    @5
    cvv
    wcel
    @7
    @3
    vy
    wmo
    #
    vx
    @3
    vx
    vy
    funopab
    @8
    @2
    wph
    vy
    wmo
    #
    wi
    @2
    wph
    wph
    vy
    vz
    wsb
    wa
    vy
    vz
    weq
    wi
    vz
    wal
    vy
    wal
    #
    @9
    @10
    vx
    cA
    isarep2.2
    rspec
    wph
    vy
    vz
    wph
    vz
    nfv
    mo3
    sylibr
    @2
    wph
    vy
    moanimv
    mpbir
    mpgbir
    @4
    cA
    isarep2.1
    funimaex
    ax-mp
    eqeltri
    isseti
end
