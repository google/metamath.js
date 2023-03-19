include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cr.mm"
include "cltrr.mm"
include "wbr.mm"
include "w3a.mm"
include "copab.mm"
include "cmnf.mm"
include "csn.mm"
include "cun.mm"
include "cpnf.mm"
include "cxp.mm"
include "wo.mm"
include "wceq.mm"
include "clt.mm"
include "wb.mm"
include "breq12.mm"
include "df-3an.mm"
include "opabbii.mm"
include "brab2a.mm"
include "a1i.mm"
include "brun.mm"
include "brxp.mm"
include "elun.mm"
include "orcom.mm"
include "bitri.mm"
include "elsng.mm"
include "orbi1d.mm"
include "syl5bb.mm"
include "bi2anan9.mm"
include "andir.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "adantr.mm"
include "orbi12d.mm"
include "orass.mm"
include "df-ltxr.mm"
include "breqi.mm"
include "3bitr4g.mm"

theorem ltxr
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A < B <-> ( ( ( ( A e. RR /\ B e. RR ) /\ A <RR B ) \/ ( A = -oo /\ B = +oo ) ) \/ ( ( A e. RR /\ B = +oo ) \/ ( A = -oo /\ B e. RR ) ) ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
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
    @3
    @5
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
    @11
    cr
    cxp
    #
    cun
    #
    wbr
    #
    wo
    #
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    cA
    cB
    cltrr
    wbr
    #
    wa
    #
    cA
    cmnf
    wceq
    #
    cB
    cpnf
    wceq
    #
    wa
    #
    @19
    @24
    wa
    #
    @23
    @20
    wa
    #
    wo
    #
    wo
    #
    wo
    cA
    cB
    clt
    wbr
    #
    @22
    @25
    wo
    @28
    wo
    @2
    @10
    @22
    @17
    @29
    @10
    @22
    wb
    @2
    @7
    @21
    vx
    vy
    cA
    cB
    cr
    cr
    @9
    @3
    cA
    @5
    cB
    cltrr
    breq12
    @8
    @4
    @6
    wa
    @7
    wa
    vx
    vy
    @4
    @6
    @7
    df-3an
    opabbii
    brab2a
    a1i
    @17
    cA
    cB
    @14
    wbr
    #
    cA
    cB
    @15
    wbr
    #
    wo
    #
    @2
    @29
    cA
    cB
    @14
    @15
    brun
    @2
    @33
    @25
    @26
    wo
    #
    @27
    wo
    @29
    @2
    @31
    @34
    @32
    @27
    @31
    cA
    @12
    wcel
    #
    cB
    @13
    wcel
    #
    wa
    #
    @2
    @34
    cA
    cB
    @12
    @13
    brxp
    @2
    @37
    @23
    @19
    wo
    #
    @24
    wa
    @34
    @0
    @35
    @38
    @1
    @36
    @24
    @35
    cA
    @11
    wcel
    #
    @19
    wo
    #
    @0
    @38
    @35
    @19
    @39
    wo
    @40
    cA
    cr
    @11
    elun
    @19
    @39
    orcom
    bitri
    @0
    @39
    @23
    @19
    cA
    cmnf
    cxr
    elsng
    #
    orbi1d
    syl5bb
    cB
    cpnf
    cxr
    elsng
    bi2anan9
    @23
    @19
    @24
    andir
    syl6bb
    syl5bb
    @32
    @39
    @20
    wa
    #
    @2
    @27
    cA
    cB
    @11
    cr
    brxp
    @0
    @42
    @27
    wb
    @1
    @0
    @39
    @23
    @20
    @41
    anbi1d
    adantr
    syl5bb
    orbi12d
    @25
    @26
    @27
    orass
    syl6bb
    syl5bb
    orbi12d
    @30
    cA
    cB
    @9
    @16
    cun
    #
    wbr
    @18
    cA
    cB
    clt
    @43
    vx
    vy
    df-ltxr
    breqi
    cA
    cB
    @9
    @16
    brun
    bitri
    @22
    @25
    @28
    orass
    3bitr4g
end
