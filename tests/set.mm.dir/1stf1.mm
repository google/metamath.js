include "c1st.mm"
include "cfv.mm"
include "cres.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cop.mm"
include "wceq.mm"
include "1stfval.mm"
include "wfun.mm"
include "cvv.mm"
include "wcel.mm"
include "wfo.mm"
include "fo1st.mm"
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

theorem 1stf1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
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
  assume 1stfval.p: |- P = ( C 1stF D )
  assume 1stf1.p: |- ( ph -> R e. B )


  assert |- ( ph -> ( ( 1st ` P ) ` R ) = ( 1st ` R ) )

  proof
    wph
    cR
    cP
    c1st
    cfv
    #
    cfv
    cR
    c1st
    cB
    cres
    #
    cfv
    #
    cR
    c1st
    cfv
    #
    wph
    cR
    @0
    @1
    wph
    cP
    @1
    vx
    vy
    cB
    cB
    c1st
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
    cP
    cT
    cH
    1stfval.t
    1stfval.b
    1stfval.h
    1stfval.c
    1stfval.d
    1stfval.p
    1stfval
    @1
    @5
    cP
    c1st
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
    c1st
    wfo
    @6
    fo1st
    cvv
    cvv
    c1st
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
    c1st
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
    1stf1.p
    cR
    cB
    c1st
    fvres
    syl
    eqtrd
end
