include "cn.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cn0.mm"
include "cfn.mm"
include "znhash.mm"
include "nnnn0.mm"
include "eqeltrd.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashclb.mm"
include "ax-mp.mm"
include "sylibr.mm"

theorem znfi
  let cB: class B
  let cN: class N
  let cY: class Y
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume zntos.y: |- Y = ( Z/nZ ` N )
  assume znhash.1: |- B = ( Base ` Y )


  assert |- ( N e. NN -> B e. Fin )

  proof
    cN
    cn
    wcel
    #
    cB
    chash
    cfv
    #
    cn0
    wcel
    #
    cB
    cfn
    wcel
    #
    @0
    @1
    cN
    cn0
    cB
    cN
    cY
    zntos.y
    znhash.1
    znhash
    cN
    nnnn0
    eqeltrd
    cB
    cvv
    wcel
    @3
    @2
    wb
    cB
    cY
    cbs
    cfv
    cvv
    znhash.1
    cY
    cbs
    fvex
    eqeltri
    cB
    cvv
    hashclb
    ax-mp
    sylibr
end
