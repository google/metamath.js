include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "c1.mm"
include "cif.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "cc.mm"
include "ax-1cn.mm"
include "keepel.mm"
include "elimne0.mm"
include "sqdivi.mm"
include "dedth.mm"

theorem sqdivzi
  let cA: class A
  let cB: class B
  assume sqdivzi.1: |- A e. CC
  assume sqdivzi.2: |- B e. CC


  assert |- ( B =/= 0 -> ( ( A / B ) ^ 2 ) = ( ( A ^ 2 ) / ( B ^ 2 ) ) )

  proof
    cB
    cc0
    wne
    #
    cA
    cB
    cdiv
    co
    #
    c2
    cexp
    co
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    cdiv
    co
    #
    wceq
    cA
    @0
    cB
    c1
    cif
    #
    cdiv
    co
    #
    c2
    cexp
    co
    #
    @3
    @6
    c2
    cexp
    co
    #
    cdiv
    co
    #
    wceq
    cB
    c1
    cB
    @6
    wceq
    #
    @2
    @8
    @5
    @10
    @11
    @1
    @7
    c2
    cexp
    cB
    @6
    cA
    cdiv
    oveq2
    oveq1d
    @11
    @4
    @9
    @3
    cdiv
    cB
    @6
    c2
    cexp
    oveq1
    oveq2d
    eqeq12d
    cA
    @6
    sqdivzi.1
    @0
    cB
    c1
    cc
    sqdivzi.2
    ax-1cn
    keepel
    cB
    elimne0
    sqdivi
    dedth
end
