include "chil.mm"
include "wcel.mm"
include "c2.mm"
include "csm.mm"
include "co.mm"
include "c1.mm"
include "cva.mm"
include "caddc.mm"
include "df-2.mm"
include "oveq1i.mm"
include "cc.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "ax-hvdistr2.mm"
include "mp3an12.mm"
include "syl5eq.mm"
include "ax-hvdistr1.mm"
include "mp3an1.mm"
include "anidms.mm"
include "hvaddcl.mm"
include "ax-hvmulid.mm"
include "syl.mm"
include "3eqtr2d.mm"

theorem hv2times
  let cA: class A


  assert |- ( A e. ~H -> ( 2 .h A ) = ( A +h A ) )

  proof
    cA
    chil
    wcel
    #
    c2
    cA
    csm
    co
    #
    c1
    cA
    csm
    co
    #
    @2
    cva
    co
    #
    c1
    cA
    cA
    cva
    co
    #
    csm
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
    cA
    csm
    co
    #
    @3
    c2
    @6
    cA
    csm
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
    cA
    ax-hvdistr2
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
    cA
    cA
    ax-hvdistr1
    mp3an1
    anidms
    @0
    @4
    chil
    wcel
    #
    @5
    @4
    wceq
    @0
    @10
    cA
    cA
    hvaddcl
    anidms
    @4
    ax-hvmulid
    syl
    3eqtr2d
end
