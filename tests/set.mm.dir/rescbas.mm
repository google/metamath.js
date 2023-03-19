include "cress.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cnx.mm"
include "chom.mm"
include "cop.mm"
include "csts.mm"
include "baseid.mm"
include "wne.mm"
include "c1.mm"
include "c4.mm"
include "cdc.mm"
include "1re.mm"
include "1nn.mm"
include "4nn0.mm"
include "1nn0.mm"
include "1lt10.mm"
include "declti.mm"
include "ltneii.mm"
include "basendx.mm"
include "homndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "wss.mm"
include "wceq.mm"
include "eqid.mm"
include "ressbas2.mm"
include "syl.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssex.mm"
include "rescval2.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"

theorem rescbas
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


  assert |- ( ph -> S = ( Base ` D ) )

  proof
    wph
    cC
    cS
    cress
    co
    #
    cbs
    cfv
    #
    @0
    cnx
    chom
    cfv
    #
    cH
    cop
    csts
    co
    #
    cbs
    cfv
    cS
    cD
    cbs
    cfv
    cH
    @2
    cbs
    @0
    baseid
    cnx
    cbs
    cfv
    #
    @2
    wne
    c1
    c1
    c4
    cdc
    #
    wne
    c1
    @5
    1re
    c1
    c4
    c1
    1nn
    4nn0
    1nn0
    1lt10
    declti
    ltneii
    @4
    c1
    @2
    @5
    basendx
    homndx
    neeq12i
    mpbir
    setsnid
    wph
    cS
    cB
    wss
    #
    cS
    @1
    wceq
    rescbas.s
    cS
    cB
    @0
    cC
    @0
    eqid
    rescbas.b
    ressbas2
    syl
    wph
    cD
    @3
    cbs
    wph
    cC
    cD
    cS
    cH
    cV
    cvv
    rescbas.d
    rescbas.c
    wph
    @6
    cS
    cvv
    wcel
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
    rescbas.h
    rescval2
    fveq2d
    3eqtr4a
end
