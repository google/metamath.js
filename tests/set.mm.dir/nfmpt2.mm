include "cmpt2.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "coprab.mm"
include "df-mpt2.mm"
include "nfcri.mm"
include "nfan.mm"
include "nfeq2.mm"
include "nfoprab.mm"
include "nfcxfr.mm"

theorem nfmpt2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  assume nfmpt2.1: |- F/_ z A
  assume nfmpt2.2: |- F/_ z B
  assume nfmpt2.3: |- F/_ z C

  disjoint x z
  disjoint y z
  disjoint w x
  disjoint w z
  disjoint w y
  disjoint A w
  disjoint B w
  disjoint C w
  assert |- F/_ z ( x e. A , y e. B |-> C )

  proof
    vz
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vx
    cv
    cA
    wcel
    #
    vy
    cv
    cB
    wcel
    #
    wa
    #
    vw
    cv
    #
    cC
    wceq
    #
    wa
    #
    vx
    vy
    vw
    coprab
    vx
    vy
    vw
    cA
    cB
    cC
    df-mpt2
    @5
    vx
    vy
    vw
    vz
    @2
    @4
    vz
    @0
    @1
    vz
    vz
    vx
    cA
    nfmpt2.1
    nfcri
    vz
    vy
    cB
    nfmpt2.2
    nfcri
    nfan
    vz
    @3
    cC
    nfmpt2.3
    nfeq2
    nfan
    nfoprab
    nfcxfr
end
