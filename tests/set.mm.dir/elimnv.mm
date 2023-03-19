include "cnv.mm"
include "wcel.mm"
include "nvzcl.mm"
include "ax-mp.mm"
include "elimel.mm"

theorem elimnv
  let cA: class A
  let cU: class U
  let cX: class X
  let cZ: class Z
  assume elimnv.1: |- X = ( BaseSet ` U )
  assume elimnv.5: |- Z = ( 0vec ` U )
  assume elimnv.9: |- U e. NrmCVec


  assert |- if ( A e. X , A , Z ) e. X

  proof
    cA
    cZ
    cX
    cU
    cnv
    wcel
    cZ
    cX
    wcel
    elimnv.9
    cU
    cX
    cZ
    elimnv.1
    elimnv.5
    nvzcl
    ax-mp
    elimel
end
