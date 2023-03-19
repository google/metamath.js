include "wcel.mm"
include "wral.mm"
include "wceq.mm"
include "cv.mm"
include "wb.mm"
include "wal.mm"
include "cmpt2.mm"
include "pm13.183.mm"
include "ralimi.mm"
include "ralbi.mm"
include "syl.mm"
include "wa.mm"
include "coprab.mm"
include "df-mpt2.mm"
include "eqeq12i.mm"
include "eqoprab2b.mm"
include "wi.mm"
include "pm5.32.mm"
include "albii.mm"
include "19.21v.mm"
include "bitr3i.mm"
include "2albii.mm"
include "r2al.mm"
include "bitr4i.mm"
include "3bitri.mm"
include "syl6rbbr.mm"

theorem mpt22eqb
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D z
  assert |- ( A. x e. A A. y e. B C e. V -> ( ( x e. A , y e. B |-> C ) = ( x e. A , y e. B |-> D ) <-> A. x e. A A. y e. B C = D ) )

  proof
    cC
    cV
    wcel
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    cC
    cD
    wceq
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    vz
    cv
    #
    cC
    wceq
    #
    @6
    cD
    wceq
    #
    wb
    #
    vz
    wal
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    vx
    vy
    cA
    cB
    cC
    cmpt2
    #
    vx
    vy
    cA
    cB
    cD
    cmpt2
    #
    wceq
    #
    @2
    @4
    @11
    wb
    #
    vx
    cA
    wral
    @5
    @12
    wb
    @1
    @16
    vx
    cA
    @1
    @3
    @10
    wb
    #
    vy
    cB
    wral
    @16
    @0
    @17
    vy
    cB
    vz
    cC
    cD
    cV
    pm13.183
    ralimi
    @3
    @10
    vy
    cB
    ralbi
    syl
    ralimi
    @4
    @11
    vx
    cA
    ralbi
    syl
    @15
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    #
    @7
    wa
    #
    vx
    vy
    vz
    coprab
    #
    @18
    @8
    wa
    #
    vx
    vy
    vz
    coprab
    #
    wceq
    @19
    @21
    wb
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    #
    @12
    @13
    @20
    @14
    @22
    vx
    vy
    vz
    cA
    cB
    cC
    df-mpt2
    vx
    vy
    vz
    cA
    cB
    cD
    df-mpt2
    eqeq12i
    @19
    @21
    vx
    vy
    vz
    eqoprab2b
    @25
    @18
    @10
    wi
    #
    vy
    wal
    vx
    wal
    @12
    @24
    @26
    vx
    vy
    @24
    @18
    @9
    wi
    #
    vz
    wal
    @26
    @27
    @23
    vz
    @18
    @7
    @8
    pm5.32
    albii
    @18
    @9
    vz
    19.21v
    bitr3i
    2albii
    @10
    vx
    vy
    cA
    cB
    r2al
    bitr4i
    3bitri
    syl6rbbr
end
