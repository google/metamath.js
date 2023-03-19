include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "elin.mm"
include "chil.mm"
include "cheli.mm"
include "adantl.mm"
include "pjcoi.mm"
include "syl.mm"
include "wi.mm"
include "cch.mm"
include "pjid.mm"
include "mpan.mm"
include "eleq1.mm"
include "syl6bir.mm"
include "eqeq2.mm"
include "sylibd.mm"
include "impcom.mm"
include "eqtrd.mm"
include "sylbi.mm"

theorem pjclem4a
  let cA: class A
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjclem1.1: |- G e. CH
  assume pjclem1.2: |- H e. CH


  assert |- ( A e. ( G i^i H ) -> ( ( ( projh ` G ) o. ( projh ` H ) ) ` A ) = A )

  proof
    cA
    cG
    cH
    cin
    wcel
    cA
    cG
    wcel
    #
    cA
    cH
    wcel
    #
    wa
    #
    cA
    cG
    cpjh
    cfv
    #
    cH
    cpjh
    cfv
    #
    ccom
    cfv
    #
    cA
    wceq
    cA
    cG
    cH
    elin
    @2
    @5
    cA
    @4
    cfv
    #
    @3
    cfv
    #
    cA
    @2
    cA
    chil
    wcel
    #
    @5
    @7
    wceq
    @1
    @8
    @0
    cA
    cH
    pjclem1.2
    cheli
    adantl
    cA
    cG
    cH
    pjclem1.1
    pjclem1.2
    pjcoi
    syl
    @1
    @0
    @7
    cA
    wceq
    #
    @1
    @6
    cA
    wceq
    #
    @0
    @9
    wi
    cH
    cch
    wcel
    @1
    @10
    pjclem1.2
    cA
    cH
    pjid
    mpan
    @10
    @0
    @7
    @6
    wceq
    #
    @9
    @10
    @0
    @6
    cG
    wcel
    #
    @11
    @6
    cA
    cG
    eleq1
    cG
    cch
    wcel
    @12
    @11
    pjclem1.1
    @6
    cG
    pjid
    mpan
    syl6bir
    @6
    cA
    @7
    eqeq2
    sylibd
    syl
    impcom
    eqtrd
    sylbi
end
