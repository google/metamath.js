include "c0.mm"
include "cop.mm"
include "cpfx.mm"
include "cdm.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cvv.mm"
include "cn0.mm"
include "cxp.mm"
include "wa.mm"
include "opelxp.mm"
include "cc0.mm"
include "csubstr.mm"
include "pfxval.mm"
include "swrd0.mm"
include "syl6eq.mm"
include "sylbi.mm"
include "cv.mm"
include "df-pfx.mm"
include "ovex.mm"
include "dmmpt2.mm"
include "eleq2s.mm"
include "wn.mm"
include "cfv.mm"
include "df-ov.mm"
include "ndmfv.mm"
include "syl5eq.mm"
include "pm2.61i.mm"

theorem pfx0
  let cL: class L
  let vl: setvar l
  let vs: setvar s
  let cS: class S
  let cV: class V
  let vk: setvar k
  let vx: setvar x


  assert |- ( (/) prefix L ) = (/)

  proof
    c0
    cL
    cop
    #
    cpfx
    cdm
    #
    wcel
    #
    c0
    cL
    cpfx
    co
    #
    c0
    wceq
    #
    @4
    @0
    cvv
    cn0
    cxp
    #
    @1
    @0
    @5
    wcel
    c0
    cvv
    wcel
    cL
    cn0
    wcel
    wa
    #
    @4
    c0
    cL
    cvv
    cn0
    opelxp
    @6
    @3
    c0
    cc0
    cL
    cop
    csubstr
    co
    c0
    c0
    cL
    cvv
    pfxval
    cc0
    cL
    swrd0
    syl6eq
    sylbi
    vs
    vl
    cvv
    cn0
    vs
    cv
    #
    cc0
    vl
    cv
    cop
    #
    csubstr
    co
    cpfx
    vs
    vl
    df-pfx
    @7
    @8
    csubstr
    ovex
    dmmpt2
    eleq2s
    @2
    wn
    @3
    @0
    cpfx
    cfv
    c0
    c0
    cL
    cpfx
    df-ov
    @0
    cpfx
    ndmfv
    syl5eq
    pm2.61i
end
