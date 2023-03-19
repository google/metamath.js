include "chil.mm"
include "wf.mm"
include "c2.mm"
include "chot.mm"
include "co.mm"
include "c1.mm"
include "chos.mm"
include "caddc.mm"
include "df-2.mm"
include "oveq1i.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "hoadddir.mm"
include "mp3an12.mm"
include "syl5eq.mm"
include "hoadddi.mm"
include "mp3an1.mm"
include "anidms.mm"
include "hoaddcl.mm"
include "homulid2.mm"
include "syl.mm"
include "3eqtr2d.mm"

theorem ho2times
  let cT: class T


  assert |- ( T : ~H --> ~H -> ( 2 .op T ) = ( T +op T ) )

  proof
    chil
    chil
    cT
    wf
    #
    c2
    cT
    chot
    co
    #
    c1
    cT
    chot
    co
    #
    @2
    chos
    co
    #
    c1
    cT
    cT
    chos
    co
    #
    chot
    co
    #
    @4
    @0
    @1
    c1
    c1
    caddc
    co
    #
    cT
    chot
    co
    #
    @3
    c2
    @6
    cT
    chot
    df-2
    oveq1i
    c1
    cc
    wcel
    #
    @8
    @0
    @7
    @3
    wceq
    ax-1cn
    ax-1cn
    c1
    c1
    cT
    hoadddir
    mp3an12
    syl5eq
    @0
    @5
    @3
    wceq
    #
    @8
    @0
    @0
    @9
    ax-1cn
    c1
    cT
    cT
    hoadddi
    mp3an1
    anidms
    @0
    chil
    chil
    @4
    wf
    #
    @5
    @4
    wceq
    @0
    @10
    cT
    cT
    hoaddcl
    anidms
    @4
    homulid2
    syl
    3eqtr2d
end
