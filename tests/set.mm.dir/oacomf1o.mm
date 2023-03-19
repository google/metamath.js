include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "coa.mm"
include "co.mm"
include "wf1o.mm"
include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "ccnv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "eqid.mm"
include "oacomf1olem.mm"
include "simpld.mm"
include "ancoms.mm"
include "f1ocnv.mm"
include "syl.mm"
include "incom.mm"
include "simprd.mm"
include "syl5eq.mm"
include "f1oun.mm"
include "syl22anc.mm"
include "wb.mm"
include "f1oeq1.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "oarec.mm"
include "f1oeq2.mm"
include "mpbird.mm"
include "uncom.mm"
include "syl6eq.mm"
include "f1oeq3.mm"

theorem oacomf1o
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume oacomf1o.1: |- F = ( ( x e. A |-> ( B +o x ) ) u. `' ( x e. B |-> ( A +o x ) ) )

  disjoint A x
  disjoint B x
  assert |- ( ( A e. On /\ B e. On ) -> F : ( A +o B ) -1-1-onto-> ( B +o A ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cA
    cB
    coa
    co
    #
    cB
    cA
    coa
    co
    #
    cF
    wf1o
    #
    @3
    vx
    cA
    cB
    vx
    cv
    #
    coa
    co
    cmpt
    #
    crn
    #
    cB
    cun
    #
    cF
    wf1o
    #
    @2
    @10
    cA
    vx
    cB
    cA
    @6
    coa
    co
    cmpt
    #
    crn
    #
    cun
    #
    @9
    cF
    wf1o
    #
    @2
    @13
    @9
    @7
    @11
    ccnv
    #
    cun
    #
    wf1o
    #
    @14
    @2
    cA
    @8
    @7
    wf1o
    #
    @12
    cB
    @15
    wf1o
    #
    cA
    @12
    cin
    #
    c0
    wceq
    @8
    cB
    cin
    c0
    wceq
    #
    @17
    @2
    @18
    @21
    vx
    cA
    cB
    @7
    @7
    eqid
    oacomf1olem
    #
    simpld
    @2
    cB
    @12
    @11
    wf1o
    #
    @19
    @2
    @23
    @12
    cA
    cin
    #
    c0
    wceq
    #
    @1
    @0
    @23
    @25
    wa
    vx
    cB
    cA
    @11
    @11
    eqid
    oacomf1olem
    ancoms
    #
    simpld
    cB
    @12
    @11
    f1ocnv
    syl
    @2
    @20
    @24
    c0
    cA
    @12
    incom
    @2
    @23
    @25
    @26
    simprd
    syl5eq
    @2
    @18
    @21
    @22
    simprd
    cA
    @8
    @12
    cB
    @7
    @15
    f1oun
    syl22anc
    cF
    @16
    wceq
    @14
    @17
    wb
    oacomf1o.1
    @13
    @9
    cF
    @16
    f1oeq1
    ax-mp
    sylibr
    @2
    @3
    @13
    wceq
    @10
    @14
    wb
    vx
    cA
    cB
    oarec
    @3
    @13
    @9
    cF
    f1oeq2
    syl
    mpbird
    @2
    @4
    @9
    wceq
    @5
    @10
    wb
    @2
    @4
    cB
    @8
    cun
    #
    @9
    @1
    @0
    @4
    @27
    wceq
    vx
    cB
    cA
    oarec
    ancoms
    cB
    @8
    uncom
    syl6eq
    @4
    @9
    @3
    cF
    f1oeq3
    syl
    mpbird
end
