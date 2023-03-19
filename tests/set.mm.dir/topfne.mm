include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "cfne.mm"
include "wbr.mm"
include "tgtop.mm"
include "sseq2d.mm"
include "bicomd.mm"
include "isfne4.mm"
include "baibr.mm"
include "sylan9bb.mm"

theorem topfne
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  assume topfne.1: |- X = U. J
  assume topfne.2: |- Y = U. K


  assert |- ( ( K e. Top /\ X = Y ) -> ( J C_ K <-> J Fne K ) )

  proof
    cK
    ctop
    wcel
    #
    cJ
    cK
    wss
    #
    cJ
    cK
    ctg
    cfv
    #
    wss
    #
    cX
    cY
    wceq
    #
    cJ
    cK
    cfne
    wbr
    #
    @0
    @3
    @1
    @0
    @2
    cK
    cJ
    cK
    tgtop
    sseq2d
    bicomd
    @5
    @4
    @3
    cJ
    cK
    cX
    cY
    topfne.1
    topfne.2
    isfne4
    baibr
    sylan9bb
end
