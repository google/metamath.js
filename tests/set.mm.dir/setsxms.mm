include "cxme.mm"
include "wcel.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cxmt.mm"
include "ctopn.mm"
include "cmopn.mm"
include "wceq.mm"
include "wb.mm"
include "setsmstopn.mm"
include "setsmsds.mm"
include "setsmsbas.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "eqid.mm"
include "isxms2.mm"
include "rbaib.mm"
include "syl.mm"
include "eleq12d.mm"
include "bitr4d.mm"

theorem setsxms
  let wph: wff ph
  let cD: class D
  let cK: class K
  let cM: class M
  let cV: class V
  let cX: class X
  let vx: setvar x
  assume setsms.x: |- ( ph -> X = ( Base ` M ) )
  assume setsms.d: |- ( ph -> D = ( ( dist ` M ) |` ( X X. X ) ) )
  assume setsms.k: |- ( ph -> K = ( M sSet <. ( TopSet ` ndx ) , ( MetOpen ` D ) >. ) )
  assume setsms.m: |- ( ph -> M e. V )


  assert |- ( ph -> ( K e. *MetSp <-> D e. ( *Met ` X ) ) )

  proof
    wph
    cK
    cxme
    wcel
    #
    cK
    cds
    cfv
    #
    cK
    cbs
    cfv
    #
    @2
    cxp
    #
    cres
    #
    @2
    cxmt
    cfv
    #
    wcel
    #
    cD
    cX
    cxmt
    cfv
    #
    wcel
    wph
    cK
    ctopn
    cfv
    #
    @4
    cmopn
    cfv
    #
    wceq
    #
    @0
    @6
    wb
    wph
    cD
    cmopn
    cfv
    @8
    @9
    wph
    cD
    cK
    cM
    cV
    cX
    setsms.x
    setsms.d
    setsms.k
    setsms.m
    setsmstopn
    wph
    cD
    @4
    cmopn
    wph
    cD
    cM
    cds
    cfv
    #
    cX
    cX
    cxp
    #
    cres
    @4
    setsms.d
    wph
    @11
    @1
    @12
    @3
    wph
    cD
    cK
    cM
    cX
    setsms.x
    setsms.d
    setsms.k
    setsmsds
    wph
    cX
    @2
    wph
    cD
    cK
    cM
    cX
    setsms.x
    setsms.d
    setsms.k
    setsmsbas
    #
    sqxpeqd
    reseq12d
    eqtrd
    #
    fveq2d
    eqtr3d
    @0
    @6
    @10
    @4
    @8
    cK
    @2
    @8
    eqid
    @2
    eqid
    @4
    eqid
    isxms2
    rbaib
    syl
    wph
    cD
    @4
    @7
    @5
    @14
    wph
    cX
    @2
    cxmt
    @13
    fveq2d
    eleq12d
    bitr4d
end
