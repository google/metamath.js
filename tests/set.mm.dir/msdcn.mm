include "cmt.mm"
include "wcel.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "cfv.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "cme.mm"
include "msmet2.mm"
include "eqid.mm"
include "metdcn2.mm"
include "syl.mm"
include "cds.mm"
include "reseq1i.mm"
include "mstopn.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"

theorem msdcn
  let cD: class D
  let cJ: class J
  let cK: class K
  let cM: class M
  let cX: class X
  assume msdcn.x: |- X = ( Base ` M )
  assume msdcn.d: |- D = ( dist ` M )
  assume msdcn.j: |- J = ( TopOpen ` M )
  assume msdcn.2: |- K = ( topGen ` ran (,) )


  assert |- ( M e. MetSp -> ( D |` ( X X. X ) ) e. ( ( J tX J ) Cn K ) )

  proof
    cM
    cmt
    wcel
    #
    cD
    cX
    cX
    cxp
    #
    cres
    #
    @2
    cmopn
    cfv
    #
    @3
    ctx
    co
    #
    cK
    ccn
    co
    #
    cJ
    cJ
    ctx
    co
    #
    cK
    ccn
    co
    @0
    @2
    cX
    cme
    cfv
    wcel
    @2
    @5
    wcel
    cD
    cM
    cX
    msdcn.x
    msdcn.d
    msmet2
    @2
    @3
    cK
    cX
    @3
    eqid
    msdcn.2
    metdcn2
    syl
    @0
    @6
    @4
    cK
    ccn
    @0
    cJ
    @3
    cJ
    @3
    ctx
    @2
    cJ
    cM
    cX
    msdcn.j
    msdcn.x
    cD
    cM
    cds
    cfv
    @1
    msdcn.d
    reseq1i
    mstopn
    #
    @7
    oveq12d
    oveq1d
    eleqtrrd
end
