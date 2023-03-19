include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "chom.mm"
include "co.mm"
include "cmpt2.mm"
include "chomf.mm"
include "reschom.mm"
include "cxp.mm"
include "wfn.mm"
include "wceq.mm"
include "rescbas.mm"
include "sqxpeqd.mm"
include "fneq12d.mm"
include "mpbid.mm"
include "fnov.mm"
include "sylib.mm"
include "eqtrd.mm"
include "eqid.mm"
include "homffval.mm"
include "syl6eqr.mm"

theorem reschomf
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cH: class H
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume rescbas.d: |- D = ( C |`cat H )
  assume rescbas.b: |- B = ( Base ` C )
  assume rescbas.c: |- ( ph -> C e. V )
  assume rescbas.h: |- ( ph -> H Fn ( S X. S ) )
  assume rescbas.s: |- ( ph -> S C_ B )


  assert |- ( ph -> H = ( Homf ` D ) )

  proof
    wph
    cH
    vx
    vy
    cD
    cbs
    cfv
    #
    @0
    vx
    cv
    vy
    cv
    cD
    chom
    cfv
    #
    co
    cmpt2
    #
    cD
    chomf
    cfv
    #
    wph
    cH
    @1
    @2
    wph
    cB
    cC
    cD
    cS
    cH
    cV
    rescbas.d
    rescbas.b
    rescbas.c
    rescbas.h
    rescbas.s
    reschom
    #
    wph
    @1
    @0
    @0
    cxp
    #
    wfn
    #
    @1
    @2
    wceq
    wph
    cH
    cS
    cS
    cxp
    #
    wfn
    @6
    rescbas.h
    wph
    @7
    @5
    cH
    @1
    @4
    wph
    cS
    @0
    wph
    cB
    cC
    cD
    cS
    cH
    cV
    rescbas.d
    rescbas.b
    rescbas.c
    rescbas.h
    rescbas.s
    rescbas
    sqxpeqd
    fneq12d
    mpbid
    vx
    vy
    @0
    @0
    @1
    fnov
    sylib
    eqtrd
    vx
    vy
    @0
    cD
    @3
    @1
    @3
    eqid
    @0
    eqid
    @1
    eqid
    homffval
    syl6eqr
end
