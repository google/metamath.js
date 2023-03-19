include "wfn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cun.mm"
include "cfv.mm"
include "wfun.mm"
include "cdm.mm"
include "fnfun.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "fndm.mm"
include "ineqan12d.mm"
include "eqeq1d.mm"
include "biimprd.mm"
include "adantrd.mm"
include "3impia.mm"
include "fvun.mm"
include "syl21anc.mm"
include "wn.mm"
include "disjel.mm"
include "adantl.mm"
include "wb.mm"
include "eleq2d.mm"
include "adantr.mm"
include "mtbird.mm"
include "3adant1.mm"
include "ndmfv.mm"
include "syl.mm"
include "uneq2d.mm"
include "un0.mm"
include "syl6eq.mm"
include "eqtrd.mm"

theorem fvun1
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cX: class X


  assert |- ( ( F Fn A /\ G Fn B /\ ( ( A i^i B ) = (/) /\ X e. A ) ) -> ( ( F u. G ) ` X ) = ( F ` X ) )

  proof
    cF
    cA
    wfn
    #
    cG
    cB
    wfn
    #
    cA
    cB
    cin
    #
    c0
    wceq
    #
    cX
    cA
    wcel
    #
    wa
    #
    w3a
    #
    cX
    cF
    cG
    cun
    cfv
    #
    cX
    cF
    cfv
    #
    cX
    cG
    cfv
    #
    cun
    #
    @8
    @6
    cF
    wfun
    #
    cG
    wfun
    #
    cF
    cdm
    #
    cG
    cdm
    #
    cin
    #
    c0
    wceq
    #
    @7
    @10
    wceq
    @0
    @1
    @11
    @5
    cA
    cF
    fnfun
    3ad2ant1
    @1
    @0
    @12
    @5
    cB
    cG
    fnfun
    3ad2ant2
    @0
    @1
    @5
    @16
    @0
    @1
    wa
    #
    @3
    @16
    @4
    @17
    @16
    @3
    @17
    @15
    @2
    c0
    @0
    @1
    @13
    cA
    @14
    cB
    cA
    cF
    fndm
    cB
    cG
    fndm
    #
    ineqan12d
    eqeq1d
    biimprd
    adantrd
    3impia
    cX
    cF
    cG
    fvun
    syl21anc
    @6
    @10
    @8
    c0
    cun
    @8
    @6
    @9
    c0
    @8
    @6
    cX
    @14
    wcel
    #
    wn
    #
    @9
    c0
    wceq
    @1
    @5
    @20
    @0
    @1
    @5
    wa
    @19
    cX
    cB
    wcel
    #
    @5
    @21
    wn
    @1
    cA
    cB
    cX
    disjel
    adantl
    @1
    @19
    @21
    wb
    @5
    @1
    @14
    cB
    cX
    @18
    eleq2d
    adantr
    mtbird
    3adant1
    cX
    cG
    ndmfv
    syl
    uneq2d
    @8
    un0
    syl6eq
    eqtrd
end
