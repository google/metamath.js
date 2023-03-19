include "cint.mm"
include "cv.mm"
include "wcel.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "cab.mm"
include "df-int.mm"
include "nfv.mm"
include "nfcrd.mm"
include "wnf.mm"
include "a1i.mm"
include "nfimd.mm"
include "nfald.mm"
include "nfabd.mm"
include "nfcxfrd.mm"

theorem nfintd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume nfintd.1: |- ( ph -> F/_ x A )


  assert |- ( ph -> F/_ x |^| A )

  proof
    wph
    vx
    cA
    cint
    vz
    cv
    cA
    wcel
    #
    vy
    vz
    wel
    #
    wi
    #
    vz
    wal
    #
    vy
    cab
    vy
    vz
    cA
    df-int
    wph
    @3
    vx
    vy
    wph
    vy
    nfv
    wph
    @2
    vx
    vz
    wph
    vz
    nfv
    wph
    @0
    @1
    vx
    wph
    vx
    vz
    cA
    nfintd.1
    nfcrd
    @1
    vx
    wnf
    wph
    @1
    vx
    nfv
    a1i
    nfimd
    nfald
    nfabd
    nfcxfrd
end
