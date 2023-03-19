include "c0.mm"
include "wne.mm"
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
include "nfcv.mm"
include "nfne.mm"
include "nfv.mm"
include "cv.mm"
include "w3a.mm"
include "simp2.mm"
include "eliin2.mm"
include "biimpar.mm"
include "rspe.mm"
include "3imp3i2an.mm"
include "sylibr.mm"
include "3exp.mm"
include "rexlimd.mm"
include "impbid2.mm"

theorem eliuniin2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cZ: class Z
  assume eliuniin2.1: |- F/_ x C
  assume eliuniin2.2: |- A = U_ x e. B |^|_ y e. C D

  disjoint A x
  disjoint C y
  disjoint Z x
  disjoint Z y
  assert |- ( C =/= (/) -> ( Z e. A <-> E. x e. B A. y e. C Z e. D ) )

  proof
    cC
    c0
    wne
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
    eliuniin2.2
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
    vx
    cC
    c0
    eliuniin2.1
    vx
    c0
    nfcv
    nfne
    @1
    vx
    nfv
    @0
    vx
    cv
    cB
    wcel
    #
    @2
    @1
    @0
    @11
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
    eliin2
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
    3exp
    rexlimd
    impbid2
end
