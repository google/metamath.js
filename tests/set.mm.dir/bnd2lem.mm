include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cbnd.mm"
include "wa.mm"
include "cxp.mm"
include "cdm.mm"
include "wss.mm"
include "cres.mm"
include "resss.mm"
include "eqsstri.mm"
include "dmss.mm"
include "mp1i.mm"
include "wceq.mm"
include "cr.mm"
include "wf.mm"
include "bndmet.mm"
include "metf.mm"
include "fdm.mm"
include "3syl.mm"
include "adantl.mm"
include "syl.mm"
include "adantr.mm"
include "3sstr3d.mm"
include "dmxpid.mm"
include "3sstr3g.mm"

theorem bnd2lem
  let cD: class D
  let cM: class M
  let cX: class X
  let cY: class Y
  assume bnd2lem.1: |- D = ( M |` ( Y X. Y ) )


  assert |- ( ( M e. ( Met ` X ) /\ D e. ( Bnd ` Y ) ) -> Y C_ X )

  proof
    cM
    cX
    cme
    cfv
    wcel
    #
    cD
    cY
    cbnd
    cfv
    wcel
    #
    wa
    #
    cY
    cY
    cxp
    #
    cdm
    #
    cX
    cX
    cxp
    #
    cdm
    #
    cY
    cX
    @2
    @3
    @5
    wss
    @4
    @6
    wss
    @2
    cD
    cdm
    #
    cM
    cdm
    #
    @3
    @5
    cD
    cM
    wss
    @7
    @8
    wss
    @2
    cD
    cM
    @3
    cres
    cM
    bnd2lem.1
    cM
    @3
    resss
    eqsstri
    cD
    cM
    dmss
    mp1i
    @1
    @7
    @3
    wceq
    #
    @0
    @1
    cD
    cY
    cme
    cfv
    wcel
    @3
    cr
    cD
    wf
    @9
    cD
    cY
    bndmet
    cD
    cY
    metf
    @3
    cr
    cD
    fdm
    3syl
    adantl
    @0
    @8
    @5
    wceq
    #
    @1
    @0
    @5
    cr
    cM
    wf
    @10
    cM
    cX
    metf
    @5
    cr
    cM
    fdm
    syl
    adantr
    3sstr3d
    @3
    @5
    dmss
    syl
    cY
    dmxpid
    cX
    dmxpid
    3sstr3g
end
