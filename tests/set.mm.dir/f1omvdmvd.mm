include "wf1o.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wne.mm"
include "csn.mm"
include "simpr.mm"
include "wfn.mm"
include "wb.mm"
include "f1ofn.mm"
include "adantr.mm"
include "wss.mm"
include "difss.mm"
include "dmss.mm"
include "ax-mp.mm"
include "f1odm.mm"
include "syl5sseq.mm"
include "sselda.mm"
include "fnelnfp.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "wf1.mm"
include "wceq.mm"
include "f1of1.mm"
include "wf.mm"
include "f1of.mm"
include "ffvelrnd.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "eldifsn.mm"
include "sylanbrc.mm"

theorem f1omvdmvd
  let cA: class A
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cG: class G


  assert |- ( ( F : A -1-1-onto-> A /\ X e. dom ( F \ _I ) ) -> ( F ` X ) e. ( dom ( F \ _I ) \ { X } ) )

  proof
    cA
    cA
    cF
    wf1o
    #
    cX
    cF
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    wa
    #
    cX
    cF
    cfv
    #
    @2
    wcel
    #
    @5
    cX
    wne
    #
    @5
    @2
    cX
    csn
    cdif
    wcel
    @4
    @6
    @5
    cF
    cfv
    #
    @5
    wne
    #
    @4
    @9
    @7
    @4
    @3
    @7
    @0
    @3
    simpr
    @4
    cF
    cA
    wfn
    #
    cX
    cA
    wcel
    #
    @3
    @7
    wb
    @0
    @10
    @3
    cA
    cA
    cF
    f1ofn
    adantr
    #
    @0
    @2
    cA
    cX
    @0
    cF
    cdm
    #
    @2
    cA
    @1
    cF
    wss
    @2
    @13
    wss
    cF
    cid
    difss
    @1
    cF
    dmss
    ax-mp
    cA
    cA
    cF
    f1odm
    syl5sseq
    sselda
    #
    cA
    cF
    cX
    fnelnfp
    syl2anc
    mpbid
    #
    @4
    @8
    @5
    @5
    cX
    @4
    cA
    cA
    cF
    wf1
    #
    @5
    cA
    wcel
    #
    @11
    @8
    @5
    wceq
    @5
    cX
    wceq
    wb
    @0
    @16
    @3
    cA
    cA
    cF
    f1of1
    adantr
    @4
    cA
    cA
    cX
    cF
    @0
    cA
    cA
    cF
    wf
    @3
    cA
    cA
    cF
    f1of
    adantr
    @14
    ffvelrnd
    #
    @14
    cA
    cA
    @5
    cX
    cF
    f1fveq
    syl12anc
    necon3bid
    mpbird
    @4
    @10
    @17
    @6
    @9
    wb
    @12
    @18
    cA
    cF
    @5
    fnelnfp
    syl2anc
    mpbird
    @15
    @5
    @2
    cX
    eldifsn
    sylanbrc
end
