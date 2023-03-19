include "cress.mm"
include "co.mm"
include "cco.mm"
include "cfv.mm"
include "cnx.mm"
include "chom.mm"
include "cop.mm"
include "csts.mm"
include "ccoid.mm"
include "wne.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "c4.mm"
include "1nn0.mm"
include "4nn.mm"
include "decnncl.mm"
include "nnrei.mm"
include "4nn0.mm"
include "5nn.mm"
include "4lt5.mm"
include "declt.mm"
include "gtneii.mm"
include "ccondx.mm"
include "homndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "wss.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssex.mm"
include "syl.mm"
include "eqid.mm"
include "ressco.mm"
include "rescval2.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"

theorem rescco
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let c.x: class .x.
  let cH: class H
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume rescbas.d: |- D = ( C |`cat H )
  assume rescbas.b: |- B = ( Base ` C )
  assume rescbas.c: |- ( ph -> C e. V )
  assume rescbas.h: |- ( ph -> H Fn ( S X. S ) )
  assume rescbas.s: |- ( ph -> S C_ B )
  assume rescco.o: |- .x. = ( comp ` C )


  assert |- ( ph -> .x. = ( comp ` D ) )

  proof
    wph
    cC
    cS
    cress
    co
    #
    cco
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
    cco
    cfv
    c.x
    cD
    cco
    cfv
    cH
    @2
    cco
    @0
    ccoid
    cnx
    cco
    cfv
    #
    @2
    wne
    c1
    c5
    cdc
    #
    c1
    c4
    cdc
    #
    wne
    @6
    @5
    @6
    c1
    c4
    1nn0
    4nn
    decnncl
    nnrei
    c1
    c4
    c5
    1nn0
    4nn0
    5nn
    4lt5
    declt
    gtneii
    @4
    @5
    @2
    @6
    ccondx
    homndx
    neeq12i
    mpbir
    setsnid
    wph
    cS
    cvv
    wcel
    #
    c.x
    @1
    wceq
    wph
    cS
    cB
    wss
    @7
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
    cS
    cC
    @0
    c.x
    cvv
    @0
    eqid
    rescco.o
    ressco
    syl
    wph
    cD
    @3
    cco
    wph
    cC
    cD
    cS
    cH
    cV
    cvv
    rescbas.d
    rescbas.c
    @8
    rescbas.h
    rescval2
    fveq2d
    3eqtr4a
end
