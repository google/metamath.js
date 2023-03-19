include "cmpt.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "df-mpt.mm"
include "nfcri.mm"
include "nfeq2.mm"
include "nfan.mm"
include "nfopab.mm"
include "nfcxfr.mm"

theorem nfmpt
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume nfmpt.1: |- F/_ x A
  assume nfmpt.2: |- F/_ x B

  disjoint x y
  disjoint A z
  disjoint B z
  disjoint x z
  disjoint y z
  assert |- F/_ x ( y e. A |-> B )

  proof
    vx
    vy
    cA
    cB
    cmpt
    vy
    cv
    cA
    wcel
    #
    vz
    cv
    #
    cB
    wceq
    #
    wa
    #
    vy
    vz
    copab
    vy
    vz
    cA
    cB
    df-mpt
    @3
    vy
    vz
    vx
    @0
    @2
    vx
    vx
    vy
    cA
    nfmpt.1
    nfcri
    vx
    @1
    cB
    nfmpt.2
    nfeq2
    nfan
    nfopab
    nfcxfr
end
