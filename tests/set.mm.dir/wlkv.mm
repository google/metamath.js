include "cv.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "cwlks.mm"
include "cvv.mm"
include "eqid.mm"
include "wksfval.mm"
include "brfvopab.mm"

theorem wlkv
  let cP: class P
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vk: setvar k
  let vp: setvar p


  assert |- ( F ( Walks ` G ) P -> ( G e. _V /\ F e. _V /\ P e. _V ) )

  proof
    vf
    cv
    #
    cG
    ciedg
    cfv
    #
    cdm
    cword
    wcel
    cc0
    @0
    chash
    cfv
    #
    cfz
    co
    cG
    cvtx
    cfv
    #
    vp
    cv
    #
    wf
    vk
    cv
    #
    @4
    cfv
    #
    @5
    c1
    caddc
    co
    @4
    cfv
    #
    wceq
    @5
    @0
    cfv
    @1
    cfv
    #
    @6
    csn
    wceq
    @6
    @7
    cpr
    @8
    wss
    wif
    vk
    cc0
    @2
    cfzo
    co
    wral
    w3a
    vf
    vp
    cF
    cP
    cwlks
    cG
    vf
    vk
    cG
    @1
    @3
    cvv
    vp
    @3
    eqid
    @1
    eqid
    wksfval
    brfvopab
end
