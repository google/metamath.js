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
include "cvv.mm"
include "cwlks.mm"
include "df-wlks.mm"
include "relmptopab.mm"

theorem relwlk
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vp: setvar p


  assert |- Rel ( Walks ` G )

  proof
    vf
    cv
    #
    vg
    cv
    #
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
    @1
    cvtx
    cfv
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
    @2
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
    @3
    cfzo
    co
    wral
    w3a
    vg
    vf
    vp
    cvv
    cG
    cwlks
    vf
    vg
    vk
    vp
    df-wlks
    relmptopab
end
