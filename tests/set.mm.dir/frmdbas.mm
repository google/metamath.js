include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cword.mm"
include "cnx.mm"
include "cop.mm"
include "cplusg.mm"
include "cconcat.mm"
include "cxp.mm"
include "cres.mm"
include "cpr.mm"
include "eqidd.mm"
include "eqid.mm"
include "frmdval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "wrdexg.mm"
include "grpbase.mm"
include "syl.mm"
include "eqtr4d.mm"
include "syl5eq.mm"

theorem frmdbas
  let cB: class B
  let cI: class I
  let cM: class M
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume frmdbas.m: |- M = ( freeMnd ` I )
  assume frmdbas.b: |- B = ( Base ` M )


  assert |- ( I e. V -> B = Word I )

  proof
    cI
    cV
    wcel
    #
    cB
    cM
    cbs
    cfv
    #
    cI
    cword
    #
    frmdbas.b
    @0
    @1
    cnx
    cbs
    cfv
    @2
    cop
    cnx
    cplusg
    cfv
    cconcat
    @2
    @2
    cxp
    cres
    #
    cop
    cpr
    #
    cbs
    cfv
    #
    @2
    @0
    cM
    @4
    cbs
    @2
    @3
    cI
    cM
    cV
    frmdbas.m
    @0
    @2
    eqidd
    @3
    eqid
    frmdval
    fveq2d
    @0
    @2
    cvv
    wcel
    @2
    @5
    wceq
    cI
    cV
    wrdexg
    @2
    @3
    @4
    cvv
    @4
    eqid
    grpbase
    syl
    eqtr4d
    syl5eq
end
