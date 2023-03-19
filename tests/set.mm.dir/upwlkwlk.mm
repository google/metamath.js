include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "cupwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cwlks.mm"
include "ciedg.mm"
include "cvtx.mm"
include "eqid.mm"
include "upwlkbprop.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "csn.mm"
include "wss.mm"
include "wif.mm"
include "idd.mm"
include "wi.mm"
include "wa.mm"
include "ifpprsnss.mm"
include "a1i.mm"
include "ralimdva.mm"
include "3anim123d.mm"
include "isupwlk.mm"
include "iswlk.mm"
include "3imtr4d.mm"
include "mpcom.mm"

theorem upwlkwlk
  let cP: class P
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x


  assert |- ( F ( UPWalks ` G ) P -> F ( Walks ` G ) P )

  proof
    cG
    cvv
    wcel
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    w3a
    #
    cF
    cP
    cG
    cupwlks
    cfv
    wbr
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cP
    cF
    cG
    cG
    ciedg
    cfv
    #
    cG
    cvtx
    cfv
    #
    @4
    eqid
    #
    @3
    eqid
    #
    upwlkbprop
    @0
    cF
    @3
    cdm
    cword
    wcel
    #
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    @4
    cP
    wf
    #
    vk
    cv
    #
    cF
    cfv
    @3
    cfv
    #
    @10
    cP
    cfv
    #
    @10
    c1
    caddc
    co
    cP
    cfv
    #
    cpr
    #
    wceq
    #
    vk
    cc0
    @8
    cfzo
    co
    #
    wral
    #
    w3a
    @7
    @9
    @12
    @13
    wceq
    @11
    @12
    csn
    wceq
    @14
    @11
    wss
    wif
    #
    vk
    @16
    wral
    #
    w3a
    @1
    @2
    @0
    @7
    @7
    @9
    @9
    @17
    @19
    @0
    @7
    idd
    @0
    @9
    idd
    @0
    @15
    @18
    vk
    @16
    @15
    @18
    wi
    @0
    @10
    @16
    wcel
    wa
    @12
    @13
    @11
    ifpprsnss
    a1i
    ralimdva
    3anim123d
    cP
    cvv
    vk
    cF
    cG
    @3
    @4
    cvv
    cvv
    @5
    @6
    isupwlk
    cP
    cvv
    vk
    cF
    cG
    @3
    @4
    cvv
    cvv
    @5
    @6
    iswlk
    3imtr4d
    mpcom
end
