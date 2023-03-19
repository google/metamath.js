include "cnv.mm"
include "wcel.mm"
include "cr.mm"
include "nvf.mm"
include "ffvelrnda.mm"

theorem nvcl
  let cA: class A
  let cU: class U
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume nvf.1: |- X = ( BaseSet ` U )
  assume nvf.6: |- N = ( normCV ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( N ` A ) e. RR )

  proof
    cU
    cnv
    wcel
    cX
    cr
    cA
    cN
    cU
    cN
    cX
    nvf.1
    nvf.6
    nvf
    ffvelrnda
end
