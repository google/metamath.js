include "c1.mm"
include "cz.mm"
include "wcel.mm"
include "c0.mm"
include "cprod.mm"
include "wceq.mm"
include "1z.mm"
include "cn.mm"
include "csn.mm"
include "cxp.mm"
include "nnuz.mm"
include "id.mm"
include "cc0.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "prodfclim1.mm"
include "wss.mm"
include "0ss.mm"
include "cv.mm"
include "wa.mm"
include "cfv.mm"
include "cif.mm"
include "fvconst2g.mm"
include "noel.mm"
include "iffalsei.mm"
include "syl6eqr.mm"
include "cc.mm"
include "pm2.21i.mm"
include "adantl.mm"
include "zprodn0.mm"
include "ax-mp.mm"

theorem prod0
  let cA: class A
  let vk: setvar k


  assert |- prod_ k e. (/) A = 1

  proof
    c1
    cz
    wcel
    #
    c0
    cA
    vk
    cprod
    c1
    wceq
    1z
    @0
    c0
    cA
    vk
    cn
    c1
    csn
    cxp
    #
    c1
    c1
    cn
    nnuz
    @0
    id
    c1
    cc0
    wne
    @0
    ax-1ne0
    a1i
    c1
    cn
    nnuz
    prodfclim1
    c0
    cn
    wss
    @0
    cn
    0ss
    a1i
    @0
    vk
    cv
    #
    cn
    wcel
    wa
    @2
    @1
    cfv
    c1
    @2
    c0
    wcel
    #
    cA
    c1
    cif
    cn
    c1
    @2
    cz
    fvconst2g
    @3
    cA
    c1
    @2
    noel
    #
    iffalsei
    syl6eqr
    @3
    cA
    cc
    wcel
    #
    @0
    @3
    @5
    @4
    pm2.21i
    adantl
    zprodn0
    ax-mp
end
