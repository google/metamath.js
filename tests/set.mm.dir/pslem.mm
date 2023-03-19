include "cps.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "cuni.mm"
include "wceq.mm"
include "cvv.mm"
include "cv.mm"
include "wal.mm"
include "wrel.mm"
include "psrel.mm"
include "brrelex12.mm"
include "sylan.mm"
include "brrelex2.mm"
include "anim12dan.mm"
include "ccom.mm"
include "wss.mm"
include "pstr2.mm"
include "cotr.mm"
include "sylib.mm"
include "adantr.mm"
include "simpr.mm"
include "w3a.mm"
include "wb.mm"
include "breq12.mm"
include "3adant3.mm"
include "3adant1.mm"
include "anbi12d.mm"
include "3adant2.mm"
include "imbi12d.mm"
include "spc3gv.mm"
include "3expa.mm"
include "syl3c.mm"
include "ex.mm"
include "ccnv.mm"
include "cin.mm"
include "cid.mm"
include "cres.mm"
include "wral.mm"
include "psref2.mm"
include "asymref2.mm"
include "simplbi.mm"
include "anidms.mm"
include "rspccv.mm"
include "3syl.mm"
include "adantrr.mm"
include "simprbi.mm"
include "syl.mm"
include "ancoms.mm"
include "eqeq12.mm"
include "spc2gv.mm"
include "3jca.mm"

theorem pslem
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R e. PosetRel -> ( ( ( A R B /\ B R C ) -> A R C ) /\ ( A e. U. U. R -> A R A ) /\ ( ( A R B /\ B R A ) -> A = B ) ) )

  proof
    cR
    cps
    wcel
    #
    cA
    cB
    cR
    wbr
    #
    cB
    cC
    cR
    wbr
    #
    wa
    #
    cA
    cC
    cR
    wbr
    #
    wi
    #
    cA
    cR
    cuni
    cuni
    #
    wcel
    cA
    cA
    cR
    wbr
    #
    wi
    #
    @1
    cB
    cA
    cR
    wbr
    #
    wa
    #
    cA
    cB
    wceq
    #
    wi
    #
    @0
    @3
    @4
    @0
    @3
    wa
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
    cC
    cvv
    wcel
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @18
    vz
    cv
    #
    cR
    wbr
    #
    wa
    #
    @17
    @20
    cR
    wbr
    #
    wi
    #
    vz
    wal
    vy
    wal
    vx
    wal
    #
    @3
    @4
    @0
    @1
    @15
    @2
    @16
    @0
    cR
    wrel
    #
    @1
    @15
    cR
    psrel
    #
    cA
    cB
    cR
    brrelex12
    sylan
    #
    @0
    @26
    @2
    @16
    @27
    cB
    cC
    cR
    brrelex2
    sylan
    anim12dan
    @0
    @25
    @3
    @0
    cR
    cR
    ccom
    cR
    wss
    @25
    cR
    pstr2
    vx
    vy
    vz
    cR
    cotr
    sylib
    adantr
    @0
    @3
    simpr
    @13
    @14
    @16
    @25
    @5
    wi
    @24
    @5
    vx
    vy
    vz
    cA
    cB
    cC
    cvv
    cvv
    cvv
    @17
    cA
    wceq
    #
    @18
    cB
    wceq
    #
    @20
    cC
    wceq
    #
    w3a
    #
    @22
    @3
    @23
    @4
    @32
    @19
    @1
    @21
    @2
    @29
    @30
    @19
    @1
    wb
    @31
    @17
    cA
    @18
    cB
    cR
    breq12
    #
    3adant3
    @30
    @31
    @21
    @2
    wb
    @29
    @18
    cB
    @20
    cC
    cR
    breq12
    3adant1
    anbi12d
    @29
    @31
    @23
    @4
    wb
    @30
    @17
    cA
    @20
    cC
    cR
    breq12
    3adant2
    imbi12d
    spc3gv
    3expa
    syl3c
    ex
    @0
    cR
    cR
    ccnv
    cin
    cid
    @6
    cres
    wceq
    #
    @17
    @17
    cR
    wbr
    #
    vx
    @6
    wral
    #
    @8
    cR
    psref2
    #
    @34
    @36
    @19
    @18
    @17
    cR
    wbr
    #
    wa
    #
    @17
    @18
    wceq
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    vx
    vy
    cR
    asymref2
    #
    simplbi
    @35
    @7
    vx
    cA
    @6
    @29
    @35
    @7
    wb
    @17
    cA
    @17
    cA
    cR
    breq12
    anidms
    rspccv
    3syl
    @0
    @10
    @11
    @0
    @10
    wa
    @15
    @42
    @10
    @11
    @0
    @1
    @15
    @9
    @28
    adantrr
    @0
    @42
    @10
    @0
    @34
    @42
    @37
    @34
    @36
    @42
    @43
    simprbi
    syl
    adantr
    @0
    @10
    simpr
    @41
    @12
    vx
    vy
    cA
    cB
    cvv
    cvv
    @29
    @30
    wa
    #
    @39
    @10
    @40
    @11
    @44
    @19
    @1
    @38
    @9
    @33
    @30
    @29
    @38
    @9
    wb
    @18
    cB
    @17
    cA
    cR
    breq12
    ancoms
    anbi12d
    @17
    cA
    @18
    cB
    eqeq12
    imbi12d
    spc2gv
    syl3c
    ex
    3jca
end
