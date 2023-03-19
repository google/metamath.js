include "ctop.mm"
include "ckgen.mm"
include "wf.mm"
include "wtru.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "wcel.mm"
include "cin.mm"
include "wi.mm"
include "cuni.mm"
include "cpw.mm"
include "wral.mm"
include "crab.mm"
include "cvv.mm"
include "wa.mm"
include "vuniex.mm"
include "pwex.mm"
include "rabex.mm"
include "a1i.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-kgen.mm"
include "cfv.mm"
include "kgenftop.mm"
include "adantl.mm"
include "fmpt2d.mm"
include "trud.mm"

theorem kgenf
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let cJ: class J
  let cK: class K


  assert |- kGen : Top --> Top

  proof
    ctop
    ctop
    ckgen
    wf
    wtru
    vj
    vx
    ctop
    vj
    cv
    #
    vk
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    vx
    cv
    #
    @1
    cin
    @2
    wcel
    wi
    vk
    @0
    cuni
    #
    cpw
    #
    wral
    #
    vx
    @5
    crab
    #
    ctop
    ckgen
    cvv
    @7
    cvv
    wcel
    wtru
    @0
    ctop
    wcel
    wa
    @6
    vx
    @5
    @4
    vj
    vuniex
    pwex
    rabex
    a1i
    ckgen
    vj
    ctop
    @7
    cmpt
    wceq
    wtru
    vx
    vj
    vk
    df-kgen
    a1i
    @3
    ctop
    wcel
    @3
    ckgen
    cfv
    ctop
    wcel
    wtru
    @3
    kgenftop
    adantl
    fmpt2d
    trud
end
