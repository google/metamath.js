include "wcel.mm"
include "ctp.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "idn2.mm"
include "w3o.mm"
include "cab.mm"
include "3mix3.mm"
include "e2.mm"
include "abid.mm"
include "e2bir.mm"
include "dftp2.mm"
include "eleq2i.mm"
include "eleq1.mm"
include "biimpd.mm"
include "e22.mm"
include "in2.mm"
include "gen11.mm"
include "19.23v.mm"
include "e1bi.mm"
include "idn1.mm"
include "elisset.mm"
include "e1a.mm"
include "id.mm"
include "e11.mm"
include "in1.mm"

theorem tpid3gVD
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x


  assert |- ( A e. B -> A e. { C , D , A } )

  proof
    cA
    cB
    wcel
    #
    cA
    cC
    cD
    cA
    ctp
    #
    wcel
    #
    @0
    vx
    cv
    #
    cA
    wceq
    #
    vx
    wex
    #
    @2
    wi
    #
    @5
    @2
    @0
    @4
    @2
    wi
    #
    vx
    wal
    @6
    @0
    @7
    vx
    @0
    @4
    @2
    @0
    @4
    @4
    @3
    @1
    wcel
    #
    @2
    @0
    @4
    idn2
    #
    @0
    @4
    @3
    @3
    cC
    wceq
    #
    @3
    cD
    wceq
    #
    @4
    w3o
    #
    vx
    cab
    #
    wcel
    #
    @8
    @0
    @4
    @12
    @14
    @0
    @4
    @4
    @12
    @9
    @4
    @10
    @11
    3mix3
    e2
    @12
    vx
    abid
    e2bir
    @1
    @13
    @3
    vx
    cC
    cD
    cA
    dftp2
    eleq2i
    e2bir
    @4
    @8
    @2
    @3
    cA
    @1
    eleq1
    biimpd
    e22
    in2
    gen11
    @4
    @2
    vx
    19.23v
    e1bi
    @0
    @0
    @5
    @0
    idn1
    vx
    cA
    cB
    elisset
    e1a
    @6
    id
    e11
    in1
end
