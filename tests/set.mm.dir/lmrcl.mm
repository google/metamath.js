include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "ctop.mm"
include "cv.mm"
include "cuni.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cres.mm"
include "wf.mm"
include "cuz.mm"
include "crn.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "copab.mm"
include "df-lm.mm"
include "dmmptss.mm"
include "cop.mm"
include "df-br.mm"
include "elfvdm.mm"
include "sylbi.mm"
include "sseldi.mm"

theorem lmrcl
  let cP: class P
  let cF: class F
  let cJ: class J
  let vj: setvar j
  let vk: setvar k
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  let vu: setvar u


  assert |- ( F ( ~~>t ` J ) P -> J e. Top )

  proof
    cF
    cP
    cJ
    clm
    cfv
    #
    wbr
    #
    clm
    cdm
    #
    ctop
    cJ
    vj
    ctop
    vf
    cv
    #
    vj
    cv
    #
    cuni
    #
    cc
    cpm
    co
    wcel
    vx
    cv
    #
    @5
    wcel
    @6
    vu
    cv
    #
    wcel
    vy
    cv
    #
    @7
    @3
    @8
    cres
    wf
    vy
    cuz
    crn
    wrex
    wi
    vu
    @4
    wral
    w3a
    vf
    vx
    copab
    clm
    vx
    vy
    vu
    vf
    vj
    df-lm
    dmmptss
    @1
    cF
    cP
    cop
    #
    @0
    wcel
    cJ
    @2
    wcel
    cF
    cP
    @0
    df-br
    @9
    cJ
    clm
    elfvdm
    sylbi
    sseldi
end
