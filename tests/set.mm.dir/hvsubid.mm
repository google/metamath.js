include "chil.mm"
include "wcel.mm"
include "cmv.mm"
include "co.mm"
include "cc0.mm"
include "csm.mm"
include "c0v.mm"
include "c1.mm"
include "cneg.mm"
include "caddc.mm"
include "cva.mm"
include "ax-hvmulid.mm"
include "oveq1d.mm"
include "cc.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "neg1cn.mm"
include "ax-hvdistr2.mm"
include "mp3an12.mm"
include "hvsubval.mm"
include "anidms.mm"
include "3eqtr4rd.mm"
include "1pneg1e0.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "ax-hvmul0.mm"
include "eqtrd.mm"

theorem hvsubid
  let cA: class A


  assert |- ( A e. ~H -> ( A -h A ) = 0h )

  proof
    cA
    chil
    wcel
    #
    cA
    cA
    cmv
    co
    #
    cc0
    cA
    csm
    co
    #
    c0v
    @0
    @1
    c1
    c1
    cneg
    #
    caddc
    co
    #
    cA
    csm
    co
    #
    @2
    @0
    c1
    cA
    csm
    co
    #
    @3
    cA
    csm
    co
    #
    cva
    co
    #
    cA
    @7
    cva
    co
    #
    @5
    @1
    @0
    @6
    cA
    @7
    cva
    cA
    ax-hvmulid
    oveq1d
    c1
    cc
    wcel
    @3
    cc
    wcel
    @0
    @5
    @8
    wceq
    ax-1cn
    neg1cn
    c1
    @3
    cA
    ax-hvdistr2
    mp3an12
    @0
    @1
    @9
    wceq
    cA
    cA
    hvsubval
    anidms
    3eqtr4rd
    @4
    cc0
    cA
    csm
    1pneg1e0
    oveq1i
    syl6eq
    cA
    ax-hvmul0
    eqtrd
end
