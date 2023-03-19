include "c2.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "2cnne0.mm"
include "divsubdir.mm"
include "mp3an.mm"
include "2m1e1.mm"
include "oveq1i.mm"
include "2div2e1.mm"
include "3eqtr3ri.mm"

theorem 1mhlfehlf



  assert |- ( 1 - ( 1 / 2 ) ) = ( 1 / 2 )

  proof
    c2
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    c2
    c2
    cdiv
    co
    #
    c1
    c2
    cdiv
    co
    #
    cmin
    co
    #
    @3
    c1
    @3
    cmin
    co
    c2
    cc
    wcel
    #
    c1
    cc
    wcel
    @5
    c2
    cc0
    wne
    wa
    @1
    @4
    wceq
    2cn
    ax-1cn
    2cnne0
    c2
    c1
    c2
    divsubdir
    mp3an
    @0
    c1
    c2
    cdiv
    2m1e1
    oveq1i
    @2
    c1
    @3
    cmin
    2div2e1
    oveq1i
    3eqtr3ri
end
