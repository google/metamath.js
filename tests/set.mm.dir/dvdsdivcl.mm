include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "wi.mm"
include "breq1.mm"
include "elrab.mm"
include "nndivdvds.mm"
include "biimpd.mm"
include "expcom.mm"
include "com23.mm"
include "imp.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "anim1i.mm"
include "ancomd.mm"
include "divconjdvds.mm"
include "syl.mm"
include "jctird.mm"
include "sylbi.mm"
include "impcom.mm"
include "sylibr.mm"

theorem dvdsdivcl
  let vx: setvar x
  let cA: class A
  let cN: class N

  disjoint A x
  disjoint N x
  assert |- ( ( N e. NN /\ A e. { x e. NN | x || N } ) -> ( N / A ) e. { x e. NN | x || N } )

  proof
    cN
    cn
    wcel
    #
    cA
    vx
    cv
    #
    cN
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    wcel
    #
    wa
    cN
    cA
    cdiv
    co
    #
    cn
    wcel
    #
    @5
    cN
    cdvds
    wbr
    #
    wa
    #
    @5
    @3
    wcel
    @4
    @0
    @8
    @4
    cA
    cn
    wcel
    #
    cA
    cN
    cdvds
    wbr
    #
    wa
    #
    @0
    @8
    wi
    @2
    @10
    vx
    cA
    cn
    @1
    cA
    cN
    cdvds
    breq1
    elrab
    @11
    @0
    @6
    @7
    @9
    @10
    @0
    @6
    wi
    @9
    @0
    @10
    @6
    @0
    @9
    @10
    @6
    wi
    @0
    @9
    wa
    @10
    @6
    cN
    cA
    nndivdvds
    biimpd
    expcom
    com23
    imp
    @11
    @10
    cA
    cc0
    wne
    #
    wa
    @7
    @11
    @12
    @10
    @9
    @12
    @10
    cA
    nnne0
    anim1i
    ancomd
    cA
    cN
    divconjdvds
    syl
    jctird
    sylbi
    impcom
    @2
    @7
    vx
    @5
    cn
    @1
    @5
    cN
    cdvds
    breq1
    elrab
    sylibr
end
