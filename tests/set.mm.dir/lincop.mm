include "wcel.mm"
include "cv.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "cmap.mm"
include "co.mm"
include "cpw.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "cvv.mm"
include "clinc.mm"
include "wceq.mm"
include "df-linc.mm"
include "a1i.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "pweqd.mm"
include "id.mm"
include "oveqd.mm"
include "mpteq2dv.mm"
include "oveq12d.mm"
include "mpt2eq123dv.mm"
include "adantl.mm"
include "elex.mm"
include "wral.mm"
include "fvex.mm"
include "pwex.mm"
include "ovexd.mm"
include "ralrimivw.mm"
include "eqid.mm"
include "mpt2exxg2.mm"
include "sylancr.mm"
include "fvmptd.mm"

theorem lincop
  let vx: setvar x
  let vv: setvar v
  let cM: class M
  let cX: class X
  let vs: setvar s
  let vm: setvar m
  let vk: setvar k

  disjoint M s
  disjoint M v
  disjoint M x
  disjoint s v
  disjoint s x
  disjoint v x
  disjoint X v
  disjoint M m
  disjoint m s
  disjoint m v
  disjoint m x
  disjoint X m
  disjoint k x
  assert |- ( M e. X -> ( linC ` M ) = ( s e. ( ( Base ` ( Scalar ` M ) ) ^m v ) , v e. ~P ( Base ` M ) |-> ( M gsum ( x e. v |-> ( ( s ` x ) ( .s ` M ) x ) ) ) ) )

  proof
    cM
    cX
    wcel
    #
    vm
    cM
    vs
    vv
    vm
    cv
    #
    csca
    cfv
    #
    cbs
    cfv
    #
    vv
    cv
    #
    cmap
    co
    #
    @1
    cbs
    cfv
    #
    cpw
    #
    @1
    vx
    @4
    vx
    cv
    #
    vs
    cv
    cfv
    #
    @8
    @1
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    vs
    vv
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    @4
    cmap
    co
    #
    cM
    cbs
    cfv
    #
    cpw
    #
    cM
    vx
    @4
    @9
    @8
    cM
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    cvv
    clinc
    cvv
    clinc
    vm
    cvv
    @14
    cmpt
    wceq
    @0
    vx
    vv
    vm
    vs
    df-linc
    a1i
    @1
    cM
    wceq
    #
    @14
    @24
    wceq
    @0
    @25
    vs
    vv
    @5
    @7
    @13
    @17
    @19
    @23
    @25
    @3
    @16
    @4
    cmap
    @25
    @2
    @15
    cbs
    @1
    cM
    csca
    fveq2
    fveq2d
    oveq1d
    @25
    @6
    @18
    @1
    cM
    cbs
    fveq2
    pweqd
    @25
    @1
    cM
    @12
    @22
    cgsu
    @25
    id
    @25
    vx
    @4
    @11
    @21
    @25
    @10
    @20
    @9
    @8
    @1
    cM
    cvsca
    fveq2
    oveqd
    mpteq2dv
    oveq12d
    mpt2eq123dv
    adantl
    cM
    cX
    elex
    @0
    @19
    cvv
    wcel
    @17
    cvv
    wcel
    #
    vv
    @19
    wral
    @24
    cvv
    wcel
    @18
    cM
    cbs
    fvex
    pwex
    @0
    @26
    vv
    @19
    @0
    @16
    @4
    cmap
    ovexd
    ralrimivw
    vs
    vv
    @17
    @19
    @23
    cvv
    cvv
    @24
    @24
    eqid
    mpt2exxg2
    sylancr
    fvmptd
end
