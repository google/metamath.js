include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crp.mm"
include "cxmt.mm"
include "cin.mm"
include "cxr.mm"
include "cbl.mm"
include "co.mm"
include "wceq.mm"
include "metxmet.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "simplr.mm"
include "sseqin2.mm"
include "sylib.mm"
include "eleqtrrd.mm"
include "rpxr.mm"
include "ad2antll.mm"
include "blres.mm"
include "syl3anc.mm"

theorem blssp
  let cR: class R
  let cS: class S
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  assume blssp.2: |- N = ( M |` ( S X. S ) )


  assert |- ( ( ( M e. ( Met ` X ) /\ S C_ X ) /\ ( Y e. S /\ R e. RR+ ) ) -> ( Y ( ball ` N ) R ) = ( ( Y ( ball ` M ) R ) i^i S ) )

  proof
    cM
    cX
    cme
    cfv
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cY
    cS
    wcel
    #
    cR
    crp
    wcel
    #
    wa
    #
    wa
    #
    cM
    cX
    cxmt
    cfv
    wcel
    #
    cY
    cX
    cS
    cin
    #
    wcel
    cR
    cxr
    wcel
    #
    cY
    cR
    cN
    cbl
    cfv
    co
    cY
    cR
    cM
    cbl
    cfv
    co
    cS
    cin
    wceq
    @0
    @7
    @1
    @5
    cM
    cX
    metxmet
    ad2antrr
    @6
    cY
    cS
    @8
    @2
    @3
    @4
    simprl
    @6
    @1
    @8
    cS
    wceq
    @0
    @1
    @5
    simplr
    cS
    cX
    sseqin2
    sylib
    eleqtrrd
    @4
    @9
    @2
    @3
    cR
    rpxr
    ad2antll
    cN
    cM
    cY
    cR
    cX
    cS
    blssp.2
    blres
    syl3anc
end
