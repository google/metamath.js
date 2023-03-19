include "csb.mm"
include "cv.mm"
include "wcel.mm"
include "wsbc.mm"
include "cab.mm"
include "df-csb.mm"
include "nfv.mm"
include "nfcrd.mm"
include "nfsbcd.mm"
include "nfabd.mm"
include "nfcxfrd.mm"

theorem nfcsbd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume nfcsbd.1: |- F/ y ph
  assume nfcsbd.2: |- ( ph -> F/_ x A )
  assume nfcsbd.3: |- ( ph -> F/_ x B )


  assert |- ( ph -> F/_ x [_ A / y ]_ B )

  proof
    wph
    vx
    vy
    cA
    cB
    csb
    vz
    cv
    cB
    wcel
    #
    vy
    cA
    wsbc
    #
    vz
    cab
    vy
    vz
    cA
    cB
    df-csb
    wph
    @1
    vx
    vz
    wph
    vz
    nfv
    wph
    @0
    vx
    vy
    cA
    nfcsbd.1
    nfcsbd.2
    wph
    vx
    vz
    cB
    nfcsbd.3
    nfcrd
    nfsbcd
    nfabd
    nfcxfrd
end
