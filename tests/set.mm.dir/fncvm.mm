include "ctop.mm"
include "cv.mm"
include "wcel.mm"
include "cuni.mm"
include "ccnv.mm"
include "cima.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cres.mm"
include "crest.mm"
include "co.mm"
include "chmeo.mm"
include "wa.mm"
include "cpw.mm"
include "wrex.mm"
include "ccn.mm"
include "crab.mm"
include "ccvm.mm"
include "df-cvm.mm"
include "ovex.mm"
include "rabex.mm"
include "fnmpt2i.mm"

theorem fncvm
  let vc: setvar c
  let vj: setvar j
  let vf: setvar f
  let vx: setvar x
  let vk: setvar k
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v


  assert |- CovMap Fn ( Top X. Top )

  proof
    vc
    vj
    ctop
    ctop
    vx
    cv
    vk
    cv
    #
    wcel
    vs
    cv
    #
    cuni
    vf
    cv
    #
    ccnv
    @0
    cima
    wceq
    vu
    cv
    #
    vv
    cv
    cin
    c0
    wceq
    vv
    @1
    @3
    csn
    cdif
    wral
    @2
    @3
    cres
    vc
    cv
    #
    @3
    crest
    co
    vj
    cv
    #
    @0
    crest
    co
    chmeo
    co
    wcel
    wa
    vu
    @1
    wral
    wa
    vs
    @4
    cpw
    c0
    csn
    cdif
    wrex
    wa
    vk
    @5
    wrex
    vx
    @5
    cuni
    wral
    #
    vf
    @4
    @5
    ccn
    co
    #
    crab
    ccvm
    vx
    vv
    vu
    vf
    vj
    vk
    vs
    vc
    df-cvm
    @6
    vf
    @7
    @4
    @5
    ccn
    ovex
    rabex
    fnmpt2i
end
