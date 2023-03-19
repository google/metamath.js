include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "weu.mm"
include "wral.mm"
include "cab.mm"
include "csn.mm"
include "wex.mm"
include "wi.mm"
include "euabsn2.mm"
include "wcel.mm"
include "eleq2.mm"
include "abid.mm"
include "velsn.mm"
include "3bitr3g.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfeq1.mm"
include "elabrex.mm"
include "elsn.mm"
include "eqcom.mm"
include "bitri.mm"
include "syl6bb.mm"
include "syl5ib.mm"
include "ralrimi.mm"
include "eqeq1.mm"
include "ralbidv.mm"
include "syl5ibrcom.mm"
include "sylbid.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "c0.mm"
include "wne.mm"
include "euex.mm"
include "rexn0.mm"
include "r19.2z.mm"
include "ex.mm"
include "3syl.mm"
include "impbid.mm"

theorem eusvobj2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume eusvobj1.1: |- B e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  assert |- ( E! x E. y e. A x = B -> ( E. y e. A x = B <-> A. y e. A x = B ) )

  proof
    vx
    cv
    #
    cB
    wceq
    #
    vy
    cA
    wrex
    #
    vx
    weu
    #
    @2
    @1
    vy
    cA
    wral
    #
    @3
    @2
    vx
    cab
    #
    vz
    cv
    #
    csn
    #
    wceq
    #
    vz
    wex
    @2
    @4
    wi
    #
    @2
    vx
    vz
    euabsn2
    @8
    @9
    vz
    @8
    @2
    @0
    @6
    wceq
    #
    @4
    @8
    @0
    @5
    wcel
    @0
    @7
    wcel
    @2
    @10
    @5
    @7
    @0
    eleq2
    @2
    vx
    abid
    vx
    @6
    velsn
    3bitr3g
    @8
    @4
    @10
    @6
    cB
    wceq
    #
    vy
    cA
    wral
    @8
    @11
    vy
    cA
    vy
    @5
    @7
    @2
    vy
    vx
    @1
    vy
    cA
    nfre1
    nfab
    nfeq1
    vy
    cv
    cA
    wcel
    cB
    @5
    wcel
    #
    @8
    @11
    vy
    vx
    cA
    cB
    eusvobj1.1
    elabrex
    @8
    @12
    cB
    @7
    wcel
    #
    @11
    @5
    @7
    cB
    eleq2
    @13
    cB
    @6
    wceq
    @11
    cB
    @6
    eusvobj1.1
    elsn
    cB
    @6
    eqcom
    bitri
    syl6bb
    syl5ib
    ralrimi
    @10
    @1
    @11
    vy
    cA
    @0
    @6
    cB
    eqeq1
    ralbidv
    syl5ibrcom
    sylbid
    exlimiv
    sylbi
    @3
    @2
    vx
    wex
    cA
    c0
    wne
    #
    @4
    @2
    wi
    @2
    vx
    euex
    @2
    @14
    vx
    @1
    vy
    cA
    rexn0
    exlimiv
    @14
    @4
    @2
    @1
    vy
    cA
    r19.2z
    ex
    3syl
    impbid
end
