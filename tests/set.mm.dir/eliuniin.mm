include "wcel.mm"
include "wral.mm"
include "wrex.mm"
include "ciin.mm"
include "ciun.mm"
include "eleq2i.mm"
include "eliun.mm"
include "sylbb.mm"
include "wi.mm"
include "eliin.mm"
include "ibi.mm"
include "a1i.mm"
include "reximdv.mm"
include "mpd.mm"
include "cv.mm"
include "w3a.mm"
include "simp2.mm"
include "biimpar.mm"
include "rspe.mm"
include "3imp3i2an.mm"
include "sylibr.mm"
include "rexlimdv3a.mm"
include "impbid2.mm"

theorem eliuniin
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cZ: class Z
  assume eliuniin.1: |- A = U_ x e. B |^|_ y e. C D

  disjoint A x
  disjoint V x
  disjoint Z x
  disjoint Z y
  assert |- ( Z e. V -> ( Z e. A <-> E. x e. B A. y e. C Z e. D ) )

  proof
    cZ
    cV
    wcel
    #
    cZ
    cA
    wcel
    #
    cZ
    cD
    wcel
    vy
    cC
    wral
    #
    vx
    cB
    wrex
    #
    @1
    cZ
    vy
    cC
    cD
    ciin
    #
    wcel
    #
    vx
    cB
    wrex
    #
    @3
    @1
    cZ
    vx
    cB
    @4
    ciun
    #
    wcel
    #
    @6
    cA
    @7
    cZ
    eliuniin.1
    eleq2i
    #
    vx
    cZ
    cB
    @4
    eliun
    #
    sylbb
    @1
    @5
    @2
    vx
    cB
    @5
    @2
    wi
    @1
    @5
    @2
    vy
    cZ
    cC
    cD
    @4
    eliin
    ibi
    a1i
    reximdv
    mpd
    @0
    @2
    @1
    vx
    cB
    @0
    vx
    cv
    cB
    wcel
    #
    @2
    w3a
    #
    @8
    @1
    @12
    @6
    @8
    @0
    @11
    @2
    @11
    @5
    @6
    @0
    @11
    @2
    simp2
    @0
    @5
    @2
    vy
    cZ
    cC
    cD
    cV
    eliin
    biimpar
    @5
    vx
    cB
    rspe
    3imp3i2an
    @10
    sylibr
    @9
    sylibr
    rexlimdv3a
    impbid2
end
