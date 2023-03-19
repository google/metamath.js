include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "caov.mm"
include "co.mm"
include "cop.mm"
include "cdm.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wceq.mm"
include "wa.mm"
include "cxp.mm"
include "wi.mm"
include "dmmpt2g.mm"
include "opelxpi.mm"
include "eleq2.mm"
include "syl5ibr.mm"
include "syl.mm"
include "impcom.mm"
include "3impa.mm"
include "mpt2fun.mm"
include "funres.mm"
include "ax-mp.mm"
include "wdfat.mm"
include "df-dfat.mm"
include "aovfundmoveq.mm"
include "sylbir.mm"
include "sylancl.mm"
include "ovmpt4g.mm"
include "eqtrd.mm"

theorem aovmpt4g
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let vk: setvar k
  assume aovmpt4g.3: |- F = ( x e. A , y e. B |-> C )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint V x
  disjoint V y
  disjoint k x
  assert |- ( ( x e. A /\ y e. B /\ C e. V ) -> (( x F y )) = C )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    cC
    cV
    wcel
    #
    w3a
    #
    @0
    @2
    cF
    caov
    #
    @0
    @2
    cF
    co
    #
    cC
    @5
    @0
    @2
    cop
    #
    cF
    cdm
    #
    wcel
    #
    cF
    @8
    csn
    #
    cres
    wfun
    #
    @6
    @7
    wceq
    #
    @1
    @3
    @4
    @10
    @4
    @1
    @3
    wa
    #
    @10
    @4
    @9
    cA
    cB
    cxp
    #
    wceq
    #
    @14
    @10
    wi
    vx
    vy
    cA
    cB
    cC
    cF
    cV
    aovmpt4g.3
    dmmpt2g
    @14
    @10
    @16
    @8
    @15
    wcel
    @0
    @2
    cA
    cB
    opelxpi
    @9
    @15
    @8
    eleq2
    syl5ibr
    syl
    impcom
    3impa
    cF
    wfun
    @12
    vx
    vy
    cA
    cB
    cC
    cF
    aovmpt4g.3
    mpt2fun
    @11
    cF
    funres
    ax-mp
    @10
    @12
    wa
    @8
    cF
    wdfat
    @13
    @8
    cF
    df-dfat
    @0
    @2
    cF
    aovfundmoveq
    sylbir
    sylancl
    vx
    vy
    cA
    cB
    cC
    cF
    cV
    aovmpt4g.3
    ovmpt4g
    eqtrd
end
