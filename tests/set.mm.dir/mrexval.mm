include "wcel.mm"
include "cmrex.mm"
include "cfv.mm"
include "cun.mm"
include "cword.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "cmcn.mm"
include "cmvar.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "uneq12d.mm"
include "wrdeq.mm"
include "syl.mm"
include "df-mrex.mm"
include "fvex.mm"
include "unex.mm"
include "wrdexi.mm"
include "fvmpt3i.mm"
include "syl5eq.mm"

theorem mrexval
  let cC: class C
  let cR: class R
  let cT: class T
  let cV: class V
  let cW: class W
  let vt: setvar t
  assume mrexval.c: |- C = ( mCN ` T )
  assume mrexval.v: |- V = ( mVR ` T )
  assume mrexval.r: |- R = ( mREx ` T )


  assert |- ( T e. W -> R = Word ( C u. V ) )

  proof
    cT
    cW
    wcel
    #
    cR
    cT
    cmrex
    cfv
    #
    cC
    cV
    cun
    #
    cword
    #
    mrexval.r
    @0
    cT
    cvv
    wcel
    @1
    @3
    wceq
    cT
    cW
    elex
    vt
    cT
    vt
    cv
    #
    cmcn
    cfv
    #
    @4
    cmvar
    cfv
    #
    cun
    #
    cword
    #
    @3
    cvv
    cmrex
    @4
    cT
    wceq
    #
    @7
    @2
    wceq
    @8
    @3
    wceq
    @9
    @5
    cC
    @6
    cV
    @9
    @5
    cT
    cmcn
    cfv
    cC
    @4
    cT
    cmcn
    fveq2
    mrexval.c
    syl6eqr
    @9
    @6
    cT
    cmvar
    cfv
    cV
    @4
    cT
    cmvar
    fveq2
    mrexval.v
    syl6eqr
    uneq12d
    @7
    @2
    wrdeq
    syl
    vt
    df-mrex
    @7
    @5
    @6
    @4
    cmcn
    fvex
    @4
    cmvar
    fvex
    unex
    wrdexi
    fvmpt3i
    syl
    syl5eq
end
