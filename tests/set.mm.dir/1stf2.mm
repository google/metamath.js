include "c1st.mm"
include "cv.mm"
include "co.mm"
include "cres.mm"
include "c2nd.mm"
include "cfv.mm"
include "cvv.mm"
include "cmpt2.mm"
include "cop.mm"
include "wceq.mm"
include "1stfval.mm"
include "wfun.mm"
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
include "op2ndd.mm"
include "syl.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "reseq2d.mm"
include "ovex.mm"
include "a1i.mm"
include "ovmpt2d.mm"

theorem 1stf2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cH: class H
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let vy: setvar y
  assume 1stfval.t: |- T = ( C Xc. D )
  assume 1stfval.b: |- B = ( Base ` T )
  assume 1stfval.h: |- H = ( Hom ` T )
  assume 1stfval.c: |- ( ph -> C e. Cat )
  assume 1stfval.d: |- ( ph -> D e. Cat )
  assume 1stfval.p: |- P = ( C 1stF D )
  assume 1stf1.p: |- ( ph -> R e. B )
  assume 1stf2.p: |- ( ph -> S e. B )


  assert |- ( ph -> ( R ( 2nd ` P ) S ) = ( 1st |` ( R H S ) ) )

  proof
    wph
    vx
    vy
    cR
    cS
    cB
    cB
    c1st
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    cres
    #
    c1st
    cR
    cS
    cH
    co
    #
    cres
    #
    cP
    c2nd
    cfv
    #
    cvv
    wph
    cP
    c1st
    cB
    cres
    #
    vx
    vy
    cB
    cB
    @3
    cmpt2
    #
    cop
    wceq
    @6
    @8
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
    @7
    @8
    cP
    c1st
    wfun
    #
    cB
    cvv
    wcel
    @7
    cvv
    wcel
    cvv
    cvv
    c1st
    wfo
    @9
    fo1st
    cvv
    cvv
    c1st
    fofun
    ax-mp
    #
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
    @3
    @11
    @11
    mpt2ex
    op2ndd
    syl
    wph
    @0
    cR
    wceq
    #
    @1
    cS
    wceq
    #
    wa
    wa
    #
    @2
    @4
    c1st
    @14
    @0
    cR
    @1
    cS
    cH
    wph
    @12
    @13
    simprl
    wph
    @12
    @13
    simprr
    oveq12d
    reseq2d
    1stf1.p
    1stf2.p
    @5
    cvv
    wcel
    #
    wph
    @9
    @4
    cvv
    wcel
    @15
    @10
    cR
    cS
    cH
    ovex
    c1st
    @4
    cvv
    resfunexg
    mp2an
    a1i
    ovmpt2d
end
