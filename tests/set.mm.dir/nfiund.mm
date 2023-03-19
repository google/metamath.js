include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "df-iun.mm"
include "nfv.mm"
include "nfcrd.mm"
include "nfrexd.mm"
include "nfabd.mm"
include "nfcxfrd.mm"

theorem nfiund
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vk: setvar k
  assume nfiund.1: |- F/ x ph
  assume nfiund.2: |- ( ph -> F/_ y A )
  assume nfiund.3: |- ( ph -> F/_ y B )


  assert |- ( ph -> F/_ y U_ x e. A B )

  proof
    wph
    vy
    vx
    cA
    cB
    ciun
    vz
    cv
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    vz
    cab
    vx
    vz
    cA
    cB
    df-iun
    wph
    @1
    vy
    vz
    wph
    vz
    nfv
    wph
    @0
    vy
    vx
    cA
    nfiund.1
    nfiund.2
    wph
    vy
    vz
    cB
    nfiund.3
    nfcrd
    nfrexd
    nfabd
    nfcxfrd
end
