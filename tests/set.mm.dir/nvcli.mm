include "cnv.mm"
include "wcel.mm"
include "cfv.mm"
include "cr.mm"
include "nvcl.mm"
include "mp2an.mm"

theorem nvcli
  let cA: class A
  let cU: class U
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume nvf.1: |- X = ( BaseSet ` U )
  assume nvf.6: |- N = ( normCV ` U )
  assume nvcli.9: |- U e. NrmCVec
  assume nvcli.7: |- A e. X


  assert |- ( N ` A ) e. RR

  proof
    cU
    cnv
    wcel
    cA
    cX
    wcel
    cA
    cN
    cfv
    cr
    wcel
    nvcli.9
    nvcli.7
    cA
    cU
    cN
    cX
    nvf.1
    nvf.6
    nvcl
    mp2an
end
