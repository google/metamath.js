include "cv.mm"
include "wcel.mm"
include "wsbc.mm"
include "cab.mm"
include "csb.mm"
include "nfcri.mm"
include "weq.mm"
include "eleq2d.mm"
include "cbvsbc.mm"
include "abbii.mm"
include "df-csb.mm"
include "3eqtr4i.mm"

theorem cbvcsb
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cD: class D
  let vz: setvar z
  assume cbvcsb.1: |- F/_ y C
  assume cbvcsb.2: |- F/_ x D
  assume cbvcsb.3: |- ( x = y -> C = D )


  assert |- [_ A / x ]_ C = [_ A / y ]_ D

  proof
    vz
    cv
    #
    cC
    wcel
    #
    vx
    cA
    wsbc
    #
    vz
    cab
    @0
    cD
    wcel
    #
    vy
    cA
    wsbc
    #
    vz
    cab
    vx
    cA
    cC
    csb
    vy
    cA
    cD
    csb
    @2
    @4
    vz
    @1
    @3
    vx
    vy
    cA
    vy
    vz
    cC
    cbvcsb.1
    nfcri
    vx
    vz
    cD
    cbvcsb.2
    nfcri
    vx
    vy
    weq
    cC
    cD
    @0
    cbvcsb.3
    eleq2d
    cbvsbc
    abbii
    vx
    vz
    cA
    cC
    df-csb
    vy
    vz
    cA
    cD
    df-csb
    3eqtr4i
end
