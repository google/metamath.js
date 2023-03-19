include "phnvi.mm"
include "elimnv.mm"

theorem elimph
  let cA: class A
  let cU: class U
  let cX: class X
  let cZ: class Z
  assume elimph.1: |- X = ( BaseSet ` U )
  assume elimph.5: |- Z = ( 0vec ` U )
  assume elimph.6: |- U e. CPreHilOLD


  assert |- if ( A e. X , A , Z ) e. X

  proof
    cA
    cU
    cX
    cZ
    elimph.1
    elimph.5
    cU
    elimph.6
    phnvi
    elimnv
end
