include "chst.mm"
include "wcel.mm"
include "cch.mm"
include "cfv.mm"
include "chil.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "w3a.mm"
include "cno.mm"
include "c0v.mm"
include "c2.mm"
include "cexp.mm"
include "wa.mm"
include "cort.mm"
include "cva.mm"
include "caddc.mm"
include "hstcl.mm"
include "choccl.mm"
include "sylan2.mm"
include "his7.mm"
include "syl3anc.mm"
include "normsq.mm"
include "syl.mm"
include "eqcomd.mm"
include "wss.mm"
include "ococ.mm"
include "eqimss2.mm"
include "jca.mm"
include "adantl.mm"
include "hstorth.mm"
include "mpdan.mm"
include "oveq12d.mm"
include "cr.mm"
include "normcl.mm"
include "resqcld.mm"
include "recnd.mm"
include "addid1d.mm"
include "3eqtrrd.mm"
include "hstoc.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "id.mm"
include "sylan9eq.mm"
include "3impa.mm"
include "wb.mm"
include "cc.mm"
include "sqeq0.mm"
include "3adant3.mm"
include "mpbid.mm"
include "hst0h.mm"

theorem hstoh
  let cA: class A
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cB: class B


  assert |- ( ( S e. CHStates /\ A e. CH /\ ( ( S ` A ) .ih ( S ` ~H ) ) = 0 ) -> ( S ` A ) = 0h )

  proof
    cS
    chst
    wcel
    #
    cA
    cch
    wcel
    #
    cA
    cS
    cfv
    #
    chil
    cS
    cfv
    #
    csp
    co
    #
    cc0
    wceq
    #
    w3a
    #
    @2
    cno
    cfv
    #
    cc0
    wceq
    #
    @2
    c0v
    wceq
    #
    @6
    @7
    c2
    cexp
    co
    #
    cc0
    wceq
    #
    @8
    @0
    @1
    @5
    @11
    @0
    @1
    wa
    #
    @5
    @10
    @4
    cc0
    @12
    @10
    @2
    @2
    cA
    cort
    cfv
    #
    cS
    cfv
    #
    cva
    co
    #
    csp
    co
    #
    @4
    @12
    @16
    @2
    @2
    csp
    co
    #
    @2
    @14
    csp
    co
    #
    caddc
    co
    #
    @10
    cc0
    caddc
    co
    @10
    @12
    @2
    chil
    wcel
    #
    @20
    @14
    chil
    wcel
    #
    @16
    @19
    wceq
    cA
    cS
    hstcl
    #
    @22
    @1
    @0
    @13
    cch
    wcel
    #
    @21
    cA
    choccl
    #
    @13
    cS
    hstcl
    sylan2
    @2
    @2
    @14
    his7
    syl3anc
    @12
    @17
    @10
    @18
    cc0
    caddc
    @12
    @10
    @17
    @12
    @20
    @10
    @17
    wceq
    @22
    @2
    normsq
    syl
    eqcomd
    @12
    @23
    cA
    @13
    cort
    cfv
    #
    wss
    #
    wa
    #
    @18
    cc0
    wceq
    @1
    @27
    @0
    @1
    @23
    @26
    @24
    @1
    @25
    cA
    wceq
    @26
    cA
    ococ
    cA
    @25
    eqimss2
    syl
    jca
    adantl
    cA
    @13
    cS
    hstorth
    mpdan
    oveq12d
    @12
    @10
    @12
    @10
    @12
    @7
    @12
    @20
    @7
    cr
    wcel
    @22
    @2
    normcl
    syl
    #
    resqcld
    recnd
    addid1d
    3eqtrrd
    @12
    @15
    @3
    @2
    csp
    cA
    cS
    hstoc
    oveq2d
    eqtrd
    @5
    id
    sylan9eq
    3impa
    @0
    @1
    @11
    @8
    wb
    #
    @5
    @12
    @7
    cc
    wcel
    @29
    @12
    @7
    @28
    recnd
    @7
    sqeq0
    syl
    3adant3
    mpbid
    @0
    @1
    @8
    @9
    wb
    @5
    cA
    cS
    hst0h
    3adant3
    mpbid
end
