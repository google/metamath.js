include "cmopn.mm"
include "cfv.mm"
include "cnx.mm"
include "cts.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "wcel.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "tsetid.mm"
include "setsid.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "eqtr4d.mm"

theorem setsmstset
  let wph: wff ph
  let cD: class D
  let cK: class K
  let cM: class M
  let cV: class V
  let cX: class X
  assume setsms.x: |- ( ph -> X = ( Base ` M ) )
  assume setsms.d: |- ( ph -> D = ( ( dist ` M ) |` ( X X. X ) ) )
  assume setsms.k: |- ( ph -> K = ( M sSet <. ( TopSet ` ndx ) , ( MetOpen ` D ) >. ) )
  assume setsms.m: |- ( ph -> M e. V )


  assert |- ( ph -> ( MetOpen ` D ) = ( TopSet ` K ) )

  proof
    wph
    cD
    cmopn
    cfv
    #
    cM
    cnx
    cts
    cfv
    @0
    cop
    csts
    co
    #
    cts
    cfv
    #
    cK
    cts
    cfv
    wph
    cM
    cV
    wcel
    @0
    cvv
    wcel
    @0
    @2
    wceq
    setsms.m
    cD
    cmopn
    fvex
    cV
    @0
    cts
    cvv
    cM
    tsetid
    setsid
    sylancl
    wph
    cK
    @1
    cts
    setsms.k
    fveq2d
    eqtr4d
end
