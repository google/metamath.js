include "csb.mm"
include "cv.mm"
include "wcel.mm"
include "wsbc.mm"
include "cab.mm"
include "df-csb.mm"
include "nfv.mm"
include "nfsbc1d.mm"
include "nfabd.mm"
include "nfcxfrd.mm"

theorem nfcsb1d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume nfcsb1d.1: |- ( ph -> F/_ x A )


  assert |- ( ph -> F/_ x [_ A / x ]_ B )

  proof
    wph
    vx
    vx
    cA
    cB
    csb
    vy
    cv
    cB
    wcel
    #
    vx
    cA
    wsbc
    #
    vy
    cab
    vx
    vy
    cA
    cB
    df-csb
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
    cA
    nfcsb1d.1
    nfsbc1d
    nfabd
    nfcxfrd
end
