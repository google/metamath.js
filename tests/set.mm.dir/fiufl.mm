include "cfn.mm"
include "wcel.mm"
include "cpw.mm"
include "cufl.mm"
include "pwfi.mm"
include "ccrd.mm"
include "cdm.mm"
include "finnum.mm"
include "numufl.mm"
include "syl.mm"
include "sylbi.mm"

theorem fiufl
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let vu: setvar u
  let vx: setvar x
  let cY: class Y


  assert |- ( X e. Fin -> X e. UFL )

  proof
    cX
    cfn
    wcel
    cX
    cpw
    #
    cfn
    wcel
    #
    cX
    cufl
    wcel
    #
    cX
    pwfi
    @1
    @0
    cpw
    #
    cfn
    wcel
    #
    @2
    @0
    pwfi
    @4
    @3
    ccrd
    cdm
    wcel
    @2
    @3
    finnum
    cX
    numufl
    syl
    sylbi
    sylbi
end
