include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "cltrr.mm"
include "w3a.mm"
include "copab.mm"
include "cmnf.mm"
include "csn.mm"
include "cun.mm"
include "cpnf.mm"
include "cxp.mm"
include "wn.mm"
include "wb.mm"
include "wo.mm"
include "brun.mm"
include "brxp.mm"
include "wceq.mm"
include "elsni.mm"
include "pnfnre.mm"
include "neli.mm"
include "simpr.mm"
include "eleq1.mm"
include "syl5ib.mm"
include "mtoi.mm"
include "syl.mm"
include "adantl.mm"
include "sylbi.mm"
include "mnfnre.mm"
include "simpl.mm"
include "adantr.mm"
include "jaoi.mm"
include "con2i.mm"
include "wi.mm"
include "biimt.mm"
include "df-ltxr.mm"
include "equncomi.mm"
include "breqi.mm"
include "df-or.mm"
include "3bitri.mm"
include "syl6rbbr.mm"
include "breq12.mm"
include "df-3an.mm"
include "opabbii.mm"
include "brab2a.mm"
include "baibr.mm"
include "bitr4d.mm"

theorem ltxrlt
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < B <-> A <RR B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    clt
    wbr
    #
    cA
    cB
    vx
    cv
    #
    cr
    wcel
    #
    vy
    cv
    #
    cr
    wcel
    #
    @4
    @6
    cltrr
    wbr
    #
    w3a
    #
    vx
    vy
    copab
    #
    wbr
    #
    cA
    cB
    cltrr
    wbr
    #
    @2
    cA
    cB
    cr
    cmnf
    csn
    #
    cun
    #
    cpnf
    csn
    #
    cxp
    #
    @13
    cr
    cxp
    #
    cun
    #
    wbr
    #
    wn
    #
    @3
    @11
    wb
    @19
    @2
    @19
    cA
    cB
    @16
    wbr
    #
    cA
    cB
    @17
    wbr
    #
    wo
    @2
    wn
    #
    cA
    cB
    @16
    @17
    brun
    @21
    @23
    @22
    @21
    cA
    @14
    wcel
    #
    cB
    @15
    wcel
    #
    wa
    @23
    cA
    cB
    @14
    @15
    brxp
    @25
    @23
    @24
    @25
    cB
    cpnf
    wceq
    #
    @23
    cB
    cpnf
    elsni
    @26
    @2
    cpnf
    cr
    wcel
    #
    cpnf
    cr
    pnfnre
    neli
    @2
    @1
    @26
    @27
    @0
    @1
    simpr
    cB
    cpnf
    cr
    eleq1
    syl5ib
    mtoi
    syl
    adantl
    sylbi
    @22
    cA
    @13
    wcel
    #
    @1
    wa
    @23
    cA
    cB
    @13
    cr
    brxp
    @28
    @23
    @1
    @28
    cA
    cmnf
    wceq
    #
    @23
    cA
    cmnf
    elsni
    @29
    @2
    cmnf
    cr
    wcel
    #
    cmnf
    cr
    mnfnre
    neli
    @2
    @0
    @29
    @30
    @0
    @1
    simpl
    cA
    cmnf
    cr
    eleq1
    syl5ib
    mtoi
    syl
    adantr
    sylbi
    jaoi
    sylbi
    con2i
    @20
    @11
    @20
    @11
    wi
    #
    @3
    @20
    @11
    biimt
    @3
    cA
    cB
    @18
    @10
    cun
    #
    wbr
    @19
    @11
    wo
    @31
    cA
    cB
    clt
    @32
    clt
    @10
    @18
    vx
    vy
    df-ltxr
    equncomi
    breqi
    cA
    cB
    @18
    @10
    brun
    @19
    @11
    df-or
    3bitri
    syl6rbbr
    syl
    @11
    @2
    @12
    @8
    @12
    vx
    vy
    cA
    cB
    cr
    cr
    @10
    @4
    cA
    @6
    cB
    cltrr
    breq12
    @9
    @5
    @7
    wa
    @8
    wa
    vx
    vy
    @5
    @7
    @8
    df-3an
    opabbii
    brab2a
    baibr
    bitr4d
end
