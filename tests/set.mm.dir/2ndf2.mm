include "c2nd.mm"
include "cv.mm"
include "co.mm"
include "cres.mm"
include "cfv.mm"
include "cvv.mm"
include "cmpt2.mm"
include "cop.mm"
include "wceq.mm"
include "2ndfval.mm"
include "wfun.mm"
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

theorem 2ndf2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
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
  assume 2ndfval.p: |- Q = ( C 2ndF D )
  assume 2ndf1.p: |- ( ph -> R e. B )
  assume 2ndf2.p: |- ( ph -> S e. B )


  assert |- ( ph -> ( R ( 2nd ` Q ) S ) = ( 2nd |` ( R H S ) ) )

  proof
    wph
    vx
    vy
    cR
    cS
    cB
    cB
    c2nd
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
    c2nd
    cR
    cS
    cH
    co
    #
    cres
    #
    cQ
    c2nd
    cfv
    #
    cvv
    wph
    cQ
    c2nd
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
    @7
    @8
    cQ
    c2nd
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
    c2nd
    wfo
    @9
    fo2nd
    cvv
    cvv
    c2nd
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
    c2nd
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
    c2nd
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
    2ndf1.p
    2ndf2.p
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
    c2nd
    @4
    cvv
    resfunexg
    mp2an
    a1i
    ovmpt2d
end
