include "cvv.mm"
include "wcel.mm"
include "cun.mm"
include "cword.mm"
include "cxp.mm"
include "wceq.mm"
include "cmrex.mm"
include "cfv.mm"
include "eqid.mm"
include "mexval.mm"
include "mrexval.mm"
include "xpeq2d.mm"
include "syl5eq.mm"
include "wn.mm"
include "c0.mm"
include "0xp.mm"
include "eqcomi.mm"
include "cmex.mm"
include "fvprc.mm"
include "cmtc.mm"
include "xpeq1d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem mexval2
  let cC: class C
  let cT: class T
  let cE: class E
  let cK: class K
  let cV: class V
  let vt: setvar t
  let cR: class R
  assume mexval.k: |- K = ( mTC ` T )
  assume mexval.e: |- E = ( mEx ` T )
  assume mexval2.c: |- C = ( mCN ` T )
  assume mexval2.v: |- V = ( mVR ` T )


  assert |- E = ( K X. Word ( C u. V ) )

  proof
    cT
    cvv
    wcel
    #
    cE
    cK
    cC
    cV
    cun
    cword
    #
    cxp
    #
    wceq
    @0
    cE
    cK
    cT
    cmrex
    cfv
    #
    cxp
    @2
    @3
    cT
    cE
    cK
    mexval.k
    mexval.e
    @3
    eqid
    #
    mexval
    @0
    @3
    @1
    cK
    cC
    @3
    cT
    cV
    cvv
    mexval2.c
    mexval2.v
    @4
    mrexval
    xpeq2d
    syl5eq
    @0
    wn
    #
    c0
    c0
    @1
    cxp
    #
    cE
    @2
    @6
    c0
    @1
    0xp
    eqcomi
    @5
    cE
    cT
    cmex
    cfv
    c0
    mexval.e
    cT
    cmex
    fvprc
    syl5eq
    @5
    cK
    c0
    @1
    @5
    cK
    cT
    cmtc
    cfv
    c0
    mexval.k
    cT
    cmtc
    fvprc
    syl5eq
    xpeq1d
    3eqtr4a
    pm2.61i
end
