include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cres.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cop.mm"
include "wceq.mm"
include "2ndfval.mm"
include "wfun.mm"
include "cvv.mm"
include "wcel.mm"
include "wfo.mm"
include "fo2nd.mm"
include "fofun.mm"
include "ax-mp.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "resfunexg.mm"
include "mp2an.mm"
include "mpt2ex.mm"
include "op1std.mm"
include "syl.mm"
include "fveq1d.mm"
include "fvres.mm"
include "eqtrd.mm"

theorem 2ndf1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cH: class H
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  assume 1stfval.t: |- T = ( C Xc. D )
  assume 1stfval.b: |- B = ( Base ` T )
  assume 1stfval.h: |- H = ( Hom ` T )
  assume 1stfval.c: |- ( ph -> C e. Cat )
  assume 1stfval.d: |- ( ph -> D e. Cat )
  assume 2ndfval.p: |- Q = ( C 2ndF D )
  assume 2ndf1.p: |- ( ph -> R e. B )


  assert |- ( ph -> ( ( 1st ` Q ) ` R ) = ( 2nd ` R ) )

  proof
    wph
    cR
    cQ
    c1st
    cfv
    #
    cfv
    cR
    c2nd
    cB
    cres
    #
    cfv
    #
    cR
    c2nd
    cfv
    #
    wph
    cR
    @0
    @1
    wph
    cQ
    @1
    vx
    vy
    cB
    cB
    c2nd
    vx
    cv
    vy
    cv
    cH
    co
    cres
    #
    cmpt2
    #
    cop
    wceq
    @0
    @1
    wceq
    wph
    vx
    vy
    cB
    cC
    cD
    cQ
    cT
    cH
    1stfval.t
    1stfval.b
    1stfval.h
    1stfval.c
    1stfval.d
    2ndfval.p
    2ndfval
    @1
    @5
    cQ
    c2nd
    wfun
    #
    cB
    cvv
    wcel
    @1
    cvv
    wcel
    cvv
    cvv
    c2nd
    wfo
    @6
    fo2nd
    cvv
    cvv
    c2nd
    fofun
    ax-mp
    cB
    cT
    cbs
    cfv
    cvv
    1stfval.b
    cT
    cbs
    fvex
    eqeltri
    #
    c2nd
    cB
    cvv
    resfunexg
    mp2an
    vx
    vy
    cB
    cB
    @4
    @7
    @7
    mpt2ex
    op1std
    syl
    fveq1d
    wph
    cR
    cB
    wcel
    @2
    @3
    wceq
    2ndf1.p
    cR
    cB
    c2nd
    fvres
    syl
    eqtrd
end
