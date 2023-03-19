include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "mulid2.mm"
include "wb.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "pm3.2i.mm"
include "divmul.mm"
include "mp3an3.mm"
include "anidms.mm"
include "mpbird.mm"

theorem div1
  let cA: class A


  assert |- ( A e. CC -> ( A / 1 ) = A )

  proof
    cA
    cc
    wcel
    #
    cA
    c1
    cdiv
    co
    cA
    wceq
    #
    c1
    cA
    cmul
    co
    cA
    wceq
    #
    cA
    mulid2
    @0
    @1
    @2
    wb
    #
    @0
    @0
    c1
    cc
    wcel
    #
    c1
    cc0
    wne
    #
    wa
    @3
    @4
    @5
    ax-1cn
    ax-1ne0
    pm3.2i
    cA
    cA
    c1
    divmul
    mp3an3
    anidms
    mpbird
end
