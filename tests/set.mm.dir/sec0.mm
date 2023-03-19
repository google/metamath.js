include "cc0.mm"
include "csec.mm"
include "cfv.mm"
include "c1.mm"
include "ccos.mm"
include "cdiv.mm"
include "co.mm"
include "cc.mm"
include "wcel.mm"
include "wne.mm"
include "wceq.mm"
include "0cn.mm"
include "cos0.mm"
include "ax-1ne0.mm"
include "eqnetri.mm"
include "secval.mm"
include "mp2an.mm"
include "oveq2i.mm"
include "1div1e1.mm"
include "3eqtri.mm"

theorem sec0
  let vk: setvar k
  let vx: setvar x


  assert |- ( sec ` 0 ) = 1

  proof
    cc0
    csec
    cfv
    #
    c1
    cc0
    ccos
    cfv
    #
    cdiv
    co
    #
    c1
    c1
    cdiv
    co
    c1
    cc0
    cc
    wcel
    @1
    cc0
    wne
    @0
    @2
    wceq
    0cn
    @1
    c1
    cc0
    cos0
    ax-1ne0
    eqnetri
    cc0
    secval
    mp2an
    @1
    c1
    c1
    cdiv
    cos0
    oveq2i
    1div1e1
    3eqtri
end
