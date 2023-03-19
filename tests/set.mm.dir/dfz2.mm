include "cz.mm"
include "cmin.mm"
include "cn.mm"
include "cxp.mm"
include "cima.mm"
include "cv.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "elz2.mm"
include "cc.mm"
include "wfn.mm"
include "wss.mm"
include "wb.mm"
include "wf.mm"
include "subf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "nnsscn.mm"
include "xpss12.mm"
include "mp2an.mm"
include "ovelimab.mm"
include "bitr4i.mm"
include "eqriv.mm"

theorem dfz2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cN: class N


  assert |- ZZ = ( - " ( NN X. NN ) )

  proof
    vx
    cz
    cmin
    cn
    cn
    cxp
    #
    cima
    #
    vx
    cv
    #
    cz
    wcel
    @2
    vy
    cv
    vz
    cv
    cmin
    co
    wceq
    vz
    cn
    wrex
    vy
    cn
    wrex
    #
    @2
    @1
    wcel
    #
    vy
    vz
    @2
    elz2
    cmin
    cc
    cc
    cxp
    #
    wfn
    #
    @0
    @5
    wss
    #
    @4
    @3
    wb
    @5
    cc
    cmin
    wf
    @6
    subf
    @5
    cc
    cmin
    ffn
    ax-mp
    cn
    cc
    wss
    #
    @8
    @7
    nnsscn
    nnsscn
    cn
    cc
    cn
    cc
    xpss12
    mp2an
    vy
    vz
    @5
    cn
    cn
    @2
    cmin
    ovelimab
    mp2an
    bitr4i
    eqriv
end
