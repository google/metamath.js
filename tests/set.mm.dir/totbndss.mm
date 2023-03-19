include "ctotbnd.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cxp.mm"
include "cres.mm"
include "cv.mm"
include "cuni.mm"
include "cbl.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "cfn.mm"
include "crp.mm"
include "cme.mm"
include "istotbnd.mm"
include "simprbi.mm"
include "sseq2.mm"
include "biimprcd.mm"
include "anim1d.mm"
include "reximdv.mm"
include "ralimdv.mm"
include "mpan9.mm"
include "wb.mm"
include "totbndmet.mm"
include "eqid.mm"
include "sstotbnd.mm"
include "sylan.mm"
include "mpbird.mm"

theorem totbndss
  let cS: class S
  let cM: class M
  let cX: class X
  let vb: setvar b
  let vd: setvar d
  let vv: setvar v
  let vx: setvar x


  assert |- ( ( M e. ( TotBnd ` X ) /\ S C_ X ) -> ( M |` ( S X. S ) ) e. ( TotBnd ` S ) )

  proof
    cM
    cX
    ctotbnd
    cfv
    wcel
    #
    cS
    cX
    wss
    #
    wa
    cM
    cS
    cS
    cxp
    cres
    #
    cS
    ctotbnd
    cfv
    wcel
    #
    cS
    vv
    cv
    #
    cuni
    #
    wss
    #
    vb
    cv
    vx
    cv
    vd
    cv
    cM
    cbl
    cfv
    co
    wceq
    vx
    cX
    wrex
    vb
    @4
    wral
    #
    wa
    #
    vv
    cfn
    wrex
    #
    vd
    crp
    wral
    #
    @0
    @5
    cX
    wceq
    #
    @7
    wa
    #
    vv
    cfn
    wrex
    #
    vd
    crp
    wral
    #
    @1
    @10
    @0
    cM
    cX
    cme
    cfv
    wcel
    #
    @14
    vx
    vv
    cM
    cX
    vb
    vd
    istotbnd
    simprbi
    @1
    @13
    @9
    vd
    crp
    @1
    @12
    @8
    vv
    cfn
    @1
    @11
    @6
    @7
    @11
    @6
    @1
    @5
    cX
    cS
    sseq2
    biimprcd
    anim1d
    reximdv
    ralimdv
    mpan9
    @0
    @15
    @1
    @3
    @10
    wb
    cM
    cX
    totbndmet
    vx
    vv
    cM
    @2
    cX
    cS
    vb
    vd
    @2
    eqid
    sstotbnd
    sylan
    mpbird
end
