include "cxme.mm"
include "wcel.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cme.mm"
include "wa.mm"
include "cxmt.mm"
include "cmt.mm"
include "setsxms.mm"
include "setsmsds.mm"
include "setsmsbas.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "eqtr2d.mm"
include "fveq2d.mm"
include "eqcomd.mm"
include "eleq12d.mm"
include "anbi12d.mm"
include "ctopn.mm"
include "eqid.mm"
include "isms.mm"
include "metxmet.mm"
include "pm4.71ri.mm"
include "3bitr4g.mm"

theorem setsms
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


  assert |- ( ph -> ( K e. MetSp <-> D e. ( Met ` X ) ) )

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
    cme
    cfv
    #
    wcel
    #
    wa
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cD
    cX
    cme
    cfv
    #
    wcel
    #
    wa
    cK
    cmt
    wcel
    @9
    wph
    @0
    @7
    @6
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
    setsxms
    wph
    @4
    cD
    @5
    @8
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
    @10
    @1
    @11
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
    eqtr2d
    wph
    @8
    @5
    wph
    cX
    @2
    cme
    @12
    fveq2d
    eqcomd
    eleq12d
    anbi12d
    @4
    cK
    ctopn
    cfv
    #
    cK
    @2
    @13
    eqid
    @2
    eqid
    @4
    eqid
    isms
    @9
    @7
    cD
    cX
    metxmet
    pm4.71ri
    3bitr4g
end
