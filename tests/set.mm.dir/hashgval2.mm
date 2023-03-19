include "chash.mm"
include "com.mm"
include "cres.mm"
include "cvv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "crdg.mm"
include "wceq.mm"
include "cfv.mm"
include "wfn.mm"
include "wral.mm"
include "wb.mm"
include "hashresfn.mm"
include "frfnom.mm"
include "eqfnfv.mm"
include "mp2an.mm"
include "wcel.mm"
include "ccrd.mm"
include "fvres.mm"
include "cfn.mm"
include "nnfi.mm"
include "eqid.mm"
include "hashgval.mm"
include "syl.mm"
include "cardnn.mm"
include "fveq2d.mm"
include "3eqtr2d.mm"
include "mprgbir.mm"

theorem hashgval2
  let vx: setvar x
  let vf: setvar f
  let vy: setvar y
  let cA: class A
  let cB: class B


  assert |- ( # |` _om ) = ( rec ( ( x e. _V |-> ( x + 1 ) ) , 0 ) |` _om )

  proof
    chash
    com
    cres
    #
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    #
    cc0
    crdg
    com
    cres
    #
    wceq
    #
    vy
    cv
    #
    @0
    cfv
    #
    @4
    @2
    cfv
    #
    wceq
    #
    vy
    com
    @0
    com
    wfn
    @2
    com
    wfn
    @3
    @7
    vy
    com
    wral
    wb
    com
    hashresfn
    cc0
    @1
    frfnom
    vy
    com
    @0
    @2
    eqfnfv
    mp2an
    @4
    com
    wcel
    #
    @5
    @4
    chash
    cfv
    #
    @4
    ccrd
    cfv
    #
    @2
    cfv
    #
    @6
    @4
    com
    chash
    fvres
    @8
    @4
    cfn
    wcel
    @11
    @9
    wceq
    @4
    nnfi
    vx
    @4
    @2
    @2
    eqid
    hashgval
    syl
    @8
    @10
    @4
    @2
    @4
    cardnn
    fveq2d
    3eqtr2d
    mprgbir
end
