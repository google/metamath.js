include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "wss.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "cbvabv.mm"
include "sseq1i.mm"
include "r19.23v.mm"
include "albii.mm"
include "ralcom4.mm"
include "abss.mm"
include "3bitr4i.mm"
include "bitr4i.mm"
include "wb.mm"
include "nfv.mm"
include "eleq1.mm"
include "ceqsalg.mm"
include "ralimi.mm"
include "ralbi.mm"
include "syl.mm"
include "syl5rbb.mm"

theorem uniiunlem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vz: setvar z

  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint x z
  disjoint C z
  assert |- ( A. x e. A B e. D -> ( A. x e. A B e. C <-> { y | E. x e. A y = B } C_ C ) )

  proof
    vy
    cv
    #
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    #
    cC
    wss
    #
    vz
    cv
    #
    cB
    wceq
    #
    @5
    cC
    wcel
    #
    wi
    #
    vz
    wal
    #
    vx
    cA
    wral
    #
    cB
    cD
    wcel
    #
    vx
    cA
    wral
    #
    cB
    cC
    wcel
    #
    vx
    cA
    wral
    #
    @4
    @6
    vx
    cA
    wrex
    #
    vz
    cab
    #
    cC
    wss
    #
    @10
    @3
    @16
    cC
    @2
    @15
    vy
    vz
    @0
    @5
    wceq
    @1
    @6
    vx
    cA
    @0
    @5
    cB
    eqeq1
    rexbidv
    cbvabv
    sseq1i
    @8
    vx
    cA
    wral
    #
    vz
    wal
    @15
    @7
    wi
    #
    vz
    wal
    @10
    @17
    @18
    @19
    vz
    @6
    @7
    vx
    cA
    r19.23v
    albii
    @8
    vx
    vz
    cA
    ralcom4
    @15
    vz
    cC
    abss
    3bitr4i
    bitr4i
    @12
    @9
    @13
    wb
    #
    vx
    cA
    wral
    @10
    @14
    wb
    @11
    @20
    vx
    cA
    @7
    @13
    vz
    cB
    cD
    @13
    vz
    nfv
    @5
    cB
    cC
    eleq1
    ceqsalg
    ralimi
    @9
    @13
    vx
    cA
    ralbi
    syl
    syl5rbb
end
