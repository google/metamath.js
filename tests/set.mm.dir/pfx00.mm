include "cc0.mm"
include "cop.mm"
include "cpfx.mm"
include "cdm.mm"
include "wcel.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "cn0.mm"
include "cxp.mm"
include "wa.mm"
include "opelxp.mm"
include "csubstr.mm"
include "pfxval.mm"
include "swrd00.mm"
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

theorem pfx00
  let cS: class S
  let cL: class L
  let vl: setvar l
  let vs: setvar s
  let cV: class V
  let vk: setvar k
  let vx: setvar x


  assert |- ( S prefix 0 ) = (/)

  proof
    cS
    cc0
    cop
    #
    cpfx
    cdm
    #
    wcel
    #
    cS
    cc0
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
    cS
    cvv
    wcel
    cc0
    cn0
    wcel
    wa
    #
    @4
    cS
    cc0
    cvv
    cn0
    opelxp
    @6
    @3
    cS
    cc0
    cc0
    cop
    csubstr
    co
    c0
    cS
    cc0
    cvv
    pfxval
    cS
    cc0
    swrd00
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
    cS
    cc0
    cpfx
    df-ov
    @0
    cpfx
    ndmfv
    syl5eq
    pm2.61i
end
