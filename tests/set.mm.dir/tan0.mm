include "cc0.mm"
include "ctan.mm"
include "cfv.mm"
include "csin.mm"
include "ccos.mm"
include "cdiv.mm"
include "co.mm"
include "cc.mm"
include "wcel.mm"
include "wne.mm"
include "wceq.mm"
include "0cn.mm"
include "c1.mm"
include "cos0.mm"
include "ax-1ne0.mm"
include "eqnetri.mm"
include "tanval.mm"
include "mp2an.mm"
include "sin0.mm"
include "oveq1i.mm"
include "ax-1cn.mm"
include "eqeltri.mm"
include "div0i.mm"
include "3eqtri.mm"

theorem tan0



  assert |- ( tan ` 0 ) = 0

  proof
    cc0
    ctan
    cfv
    #
    cc0
    csin
    cfv
    #
    cc0
    ccos
    cfv
    #
    cdiv
    co
    #
    cc0
    @2
    cdiv
    co
    cc0
    cc0
    cc
    wcel
    @2
    cc0
    wne
    @0
    @3
    wceq
    0cn
    @2
    c1
    cc0
    cos0
    ax-1ne0
    eqnetri
    #
    cc0
    tanval
    mp2an
    @1
    cc0
    @2
    cdiv
    sin0
    oveq1i
    @2
    @2
    c1
    cc
    cos0
    ax-1cn
    eqeltri
    @4
    div0i
    3eqtri
end
