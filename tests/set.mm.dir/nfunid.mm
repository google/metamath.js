include "cuni.mm"
include "wel.mm"
include "wrex.mm"
include "cab.mm"
include "dfuni2.mm"
include "nfv.mm"
include "nfvd.mm"
include "nfrexd.mm"
include "nfabd.mm"
include "nfcxfrd.mm"

theorem nfunid
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  assume nfunid.3: |- ( ph -> F/_ x A )


  assert |- ( ph -> F/_ x U. A )

  proof
    wph
    vx
    cA
    cuni
    vy
    vz
    wel
    #
    vz
    cA
    wrex
    #
    vy
    cab
    vy
    vz
    cA
    dfuni2
    wph
    @1
    vx
    vy
    wph
    vy
    nfv
    wph
    @0
    vx
    vz
    cA
    wph
    vz
    nfv
    nfunid.3
    wph
    @0
    vx
    nfvd
    nfrexd
    nfabd
    nfcxfrd
end
