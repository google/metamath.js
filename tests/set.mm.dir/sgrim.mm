include "wcel.mm"
include "cds.mm"
include "cfv.mm"
include "ressds.mm"
include "syl6reqr.mm"

theorem sgrim
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cX: class X
  assume sgrim.x: |- X = ( T |`s U )
  assume sgrim.d: |- D = ( dist ` T )
  assume sgrim.e: |- E = ( dist ` X )


  assert |- ( U e. S -> E = D )

  proof
    cU
    cS
    wcel
    cD
    cX
    cds
    cfv
    cE
    cU
    cD
    cT
    cX
    cS
    sgrim.x
    sgrim.d
    ressds
    sgrim.e
    syl6reqr
end
