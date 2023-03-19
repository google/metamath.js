include "c0.mm"
include "csu.mm"
include "caddc.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "cli.mm"
include "wceq.mm"
include "wtru.mm"
include "cn.mm"
include "nnuz.mm"
include "cz.mm"
include "wcel.mm"
include "1z.mm"
include "a1i.mm"
include "wss.mm"
include "0ss.mm"
include "cv.mm"
include "wa.mm"
include "cif.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "syl.mm"
include "noel.mm"
include "iffalsei.mm"
include "syl6eqr.mm"
include "cc.mm"
include "pm2.21i.mm"
include "adantl.mm"
include "zsum.mm"
include "trud.mm"
include "wfun.mm"
include "wbr.mm"
include "cdm.mm"
include "wf.mm"
include "fclim.mm"
include "ffun.mm"
include "ax-mp.mm"
include "serclim0.mm"
include "funbrfv.mm"
include "mp2.mm"
include "eqtri.mm"

theorem sum0
  let cA: class A
  let vk: setvar k


  assert |- sum_ k e. (/) A = 0

  proof
    c0
    cA
    vk
    csu
    #
    caddc
    c1
    cuz
    cfv
    #
    cc0
    csn
    cxp
    #
    c1
    cseq
    #
    cli
    cfv
    #
    cc0
    @0
    @4
    wceq
    wtru
    c0
    cA
    vk
    @2
    c1
    cn
    nnuz
    c1
    cz
    wcel
    #
    wtru
    1z
    a1i
    c0
    cn
    wss
    wtru
    cn
    0ss
    a1i
    wtru
    vk
    cv
    #
    cn
    wcel
    #
    wa
    #
    @6
    @2
    cfv
    #
    cc0
    @6
    c0
    wcel
    #
    cA
    cc0
    cif
    @8
    @6
    @1
    wcel
    @9
    cc0
    wceq
    @8
    @6
    cn
    @1
    wtru
    @7
    simpr
    nnuz
    syl6eleq
    @1
    cc0
    @6
    c0ex
    fvconst2
    syl
    @10
    cA
    cc0
    @6
    noel
    #
    iffalsei
    syl6eqr
    @10
    cA
    cc
    wcel
    #
    wtru
    @10
    @12
    @11
    pm2.21i
    adantl
    zsum
    trud
    cli
    wfun
    #
    @3
    cc0
    cli
    wbr
    #
    @4
    cc0
    wceq
    cli
    cdm
    #
    cc
    cli
    wf
    @13
    fclim
    @15
    cc
    cli
    ffun
    ax-mp
    @5
    @14
    1z
    c1
    serclim0
    ax-mp
    @3
    cc0
    cli
    funbrfv
    mp2
    eqtri
end
