include "cin.mm"
include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "coass.mm"
include "fveq1i.mm"
include "wceq.mm"
include "wa.mm"
include "elin.mm"
include "chil.mm"
include "cheli.mm"
include "adantr.mm"
include "pjfi.mm"
include "hocofi.mm"
include "hocoi.mm"
include "syl.mm"
include "wi.mm"
include "pjclem4a.mm"
include "eleq1.mm"
include "cch.mm"
include "pjid.mm"
include "mpan.mm"
include "syl6bir.mm"
include "eqeq2.mm"
include "sylibd.mm"
include "impcom.mm"
include "eqtrd.mm"
include "sylbi.mm"
include "inass.mm"
include "eleq2s.mm"
include "syl5eq.mm"

theorem pj3lem1
  let cA: class A
  let cF: class F
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjadj2co.1: |- F e. CH
  assume pjadj2co.2: |- G e. CH
  assume pjadj2co.3: |- H e. CH


  assert |- ( A e. ( ( F i^i G ) i^i H ) -> ( ( ( ( projh ` F ) o. ( projh ` G ) ) o. ( projh ` H ) ) ` A ) = A )

  proof
    cA
    cF
    cG
    cin
    cH
    cin
    #
    wcel
    cA
    cF
    cpjh
    cfv
    #
    cG
    cpjh
    cfv
    #
    ccom
    cH
    cpjh
    cfv
    #
    ccom
    #
    cfv
    cA
    @1
    @2
    @3
    ccom
    #
    ccom
    #
    cfv
    #
    cA
    cA
    @4
    @6
    @1
    @2
    @3
    coass
    fveq1i
    @7
    cA
    wceq
    #
    cA
    cF
    cG
    cH
    cin
    #
    cin
    #
    @0
    cA
    @10
    wcel
    cA
    cF
    wcel
    #
    cA
    @9
    wcel
    #
    wa
    #
    @8
    cA
    cF
    @9
    elin
    @13
    @7
    cA
    @5
    cfv
    #
    @1
    cfv
    #
    cA
    @13
    cA
    chil
    wcel
    #
    @7
    @15
    wceq
    @11
    @16
    @12
    cA
    cF
    pjadj2co.1
    cheli
    adantr
    cA
    @1
    @5
    cF
    pjadj2co.1
    pjfi
    @2
    @3
    cG
    pjadj2co.2
    pjfi
    cH
    pjadj2co.3
    pjfi
    hocofi
    hocoi
    syl
    @12
    @11
    @15
    cA
    wceq
    #
    @12
    @14
    cA
    wceq
    #
    @11
    @17
    wi
    cA
    cG
    cH
    pjadj2co.2
    pjadj2co.3
    pjclem4a
    @18
    @11
    @15
    @14
    wceq
    #
    @17
    @18
    @11
    @14
    cF
    wcel
    #
    @19
    @14
    cA
    cF
    eleq1
    cF
    cch
    wcel
    @20
    @19
    pjadj2co.1
    @14
    cF
    pjid
    mpan
    syl6bir
    @14
    cA
    @15
    eqeq2
    sylibd
    syl
    impcom
    eqtrd
    sylbi
    cF
    cG
    cH
    inass
    eleq2s
    syl5eq
end
