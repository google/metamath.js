include "cvol.mm"
include "cdm.mm"
include "csalg.mm"
include "wcel.mm"
include "wtru.mm"
include "cvv.mm"
include "cr.mm"
include "cpw.mm"
include "reex.mm"
include "pwex.mm"
include "dmvolss.mm"
include "ssexi.mm"
include "a1i.mm"
include "c0.mm"
include "0mbl.mm"
include "cuni.mm"
include "unidmvol.mm"
include "eqcomi.mm"
include "cv.mm"
include "cdif.mm"
include "cmmbl.mm"
include "adantl.mm"
include "cn.mm"
include "wf.mm"
include "cfv.mm"
include "ciun.mm"
include "wral.mm"
include "ffvelrn.mm"
include "ralrimiva.mm"
include "iunmbl.mm"
include "syl.mm"
include "issalnnd.mm"
include "trud.mm"

theorem dmvolsal
  let ve: setvar e
  let vn: setvar n
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x


  assert |- dom vol e. SAlg

  proof
    cvol
    cdm
    #
    csalg
    wcel
    wtru
    vy
    @0
    ve
    vn
    cvv
    cr
    @0
    cvv
    wcel
    wtru
    @0
    cr
    cpw
    cr
    reex
    pwex
    dmvolss
    ssexi
    a1i
    c0
    @0
    wcel
    wtru
    0mbl
    a1i
    @0
    cuni
    cr
    unidmvol
    eqcomi
    vy
    cv
    #
    @0
    wcel
    cr
    @1
    cdif
    @0
    wcel
    wtru
    @1
    cmmbl
    adantl
    cn
    @0
    ve
    cv
    #
    wf
    #
    vn
    cn
    vn
    cv
    #
    @2
    cfv
    #
    ciun
    @0
    wcel
    #
    wtru
    @3
    @5
    @0
    wcel
    #
    vn
    cn
    wral
    @6
    @3
    @7
    vn
    cn
    cn
    @0
    @4
    @2
    ffvelrn
    ralrimiva
    @5
    vn
    iunmbl
    syl
    adantl
    issalnnd
    trud
end
