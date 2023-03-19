include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "cima.mm"
include "crn.mm"
include "imassrn.mm"
include "cxp.mm"
include "wss.mm"
include "ustssxp.mm"
include "3adant3.mm"
include "rnss.mm"
include "rnxpid.mm"
include "syl6sseq.mm"
include "syl.mm"
include "syl5ss.mm"

theorem ustimasn
  let cP: class P
  let cU: class U
  let cV: class V
  let cX: class X


  assert |- ( ( U e. ( UnifOn ` X ) /\ V e. U /\ P e. X ) -> ( V " { P } ) C_ X )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cV
    cU
    wcel
    #
    cP
    cX
    wcel
    #
    w3a
    #
    cV
    cP
    csn
    #
    cima
    cV
    crn
    #
    cX
    cV
    @4
    imassrn
    @3
    cV
    cX
    cX
    cxp
    #
    wss
    #
    @5
    cX
    wss
    @0
    @1
    @7
    @2
    cU
    cV
    cX
    ustssxp
    3adant3
    @7
    @5
    @6
    crn
    cX
    cV
    @6
    rnss
    cX
    rnxpid
    syl6sseq
    syl
    syl5ss
end
