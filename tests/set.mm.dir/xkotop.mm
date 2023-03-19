include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "cxko.mm"
include "co.mm"
include "cv.mm"
include "crest.mm"
include "ccmp.mm"
include "cuni.mm"
include "cpw.mm"
include "crab.mm"
include "cima.mm"
include "wss.mm"
include "ccn.mm"
include "cmpt2.mm"
include "crn.mm"
include "cfi.mm"
include "cfv.mm"
include "ctg.mm"
include "eqid.mm"
include "xkoval.mm"
include "ctb.mm"
include "fibas.mm"
include "tgcl.mm"
include "ax-mp.mm"
include "syl6eqel.mm"

theorem xkotop
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vk: setvar k
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cU: class U
  let cX: class X


  assert |- ( ( R e. Top /\ S e. Top ) -> ( S ^ko R ) e. Top )

  proof
    cR
    ctop
    wcel
    cS
    ctop
    wcel
    wa
    cS
    cR
    cxko
    co
    vk
    vv
    cR
    vx
    cv
    crest
    co
    ccmp
    wcel
    vx
    cR
    cuni
    #
    cpw
    crab
    #
    cS
    vf
    cv
    vk
    cv
    cima
    vv
    cv
    wss
    vf
    cR
    cS
    ccn
    co
    crab
    cmpt2
    #
    crn
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    ctop
    vx
    vv
    cR
    cS
    @2
    vf
    vk
    @1
    @0
    @0
    eqid
    @1
    eqid
    @2
    eqid
    xkoval
    @4
    ctb
    wcel
    @5
    ctop
    wcel
    @3
    fibas
    @4
    tgcl
    ax-mp
    syl6eqel
end
