include "cress.mm"
include "co.mm"
include "cnx.mm"
include "chom.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "ovex.mm"
include "cxp.mm"
include "wfn.mm"
include "wss.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssex.mm"
include "syl.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "fnex.mm"
include "homid.mm"
include "setsid.mm"
include "sylancr.mm"
include "rescval2.mm"
include "fveq2d.mm"
include "eqtr4d.mm"

theorem reschom
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


  assert |- ( ph -> H = ( Hom ` D ) )

  proof
    wph
    cH
    cC
    cS
    cress
    co
    #
    cnx
    chom
    cfv
    cH
    cop
    csts
    co
    #
    chom
    cfv
    #
    cD
    chom
    cfv
    wph
    @0
    cvv
    wcel
    cH
    cvv
    wcel
    #
    cH
    @2
    wceq
    cC
    cS
    cress
    ovex
    wph
    cH
    cS
    cS
    cxp
    #
    wfn
    @4
    cvv
    wcel
    #
    @3
    rescbas.h
    wph
    cS
    cvv
    wcel
    #
    @6
    @5
    wph
    cS
    cB
    wss
    @6
    rescbas.s
    cS
    cB
    cB
    cC
    cbs
    cfv
    cvv
    rescbas.b
    cC
    cbs
    fvex
    eqeltri
    ssex
    syl
    #
    @7
    cS
    cS
    cvv
    cvv
    xpexg
    syl2anc
    @4
    cvv
    cH
    fnex
    syl2anc
    cvv
    cH
    chom
    cvv
    @0
    homid
    setsid
    sylancr
    wph
    cD
    @1
    chom
    wph
    cC
    cD
    cS
    cH
    cV
    cvv
    rescbas.d
    rescbas.c
    @7
    rescbas.h
    rescval2
    fveq2d
    eqtr4d
end
