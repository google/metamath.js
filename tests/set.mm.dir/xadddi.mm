include "cr.mm"
include "wcel.mm"
include "cxr.mm"
include "w3a.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cxad.mm"
include "co.mm"
include "cxmu.mm"
include "wceq.mm"
include "xadddilem.mm"
include "wa.mm"
include "simpl2.mm"
include "simpl3.mm"
include "xaddcl.mm"
include "syl2anc.mm"
include "xmul02.mm"
include "syl.mm"
include "0xr.mm"
include "xaddid1.mm"
include "ax-mp.mm"
include "syl6eqr.mm"
include "simpr.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"
include "cxne.mm"
include "simp1.mm"
include "adantr.mm"
include "cneg.mm"
include "rexneg.mm"
include "renegcl.mm"
include "eqeltrd.mm"
include "wb.mm"
include "rexrd.mm"
include "xlt0neg1.mm"
include "biimpa.mm"
include "syl31anc.mm"
include "xmulneg1.mm"
include "xmulcl.mm"
include "xnegdi.mm"
include "eqtr4d.mm"
include "xneg11.mm"
include "mpbid.mm"
include "w3o.mm"
include "0re.mm"
include "lttri4.mm"
include "sylancr.mm"
include "mpjao3dan.mm"

theorem xadddi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR* /\ C e. RR* ) -> ( A *e ( B +e C ) ) = ( ( A *e B ) +e ( A *e C ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    #
    cc0
    cA
    clt
    wbr
    #
    cA
    cB
    cC
    cxad
    co
    #
    cxmu
    co
    #
    cA
    cB
    cxmu
    co
    #
    cA
    cC
    cxmu
    co
    #
    cxad
    co
    #
    wceq
    #
    cc0
    cA
    wceq
    #
    cA
    cc0
    clt
    wbr
    #
    cA
    cB
    cC
    xadddilem
    @3
    @11
    wa
    #
    cc0
    @5
    cxmu
    co
    #
    cc0
    cc0
    cxad
    co
    #
    @6
    @9
    @13
    @14
    cc0
    @15
    @13
    @5
    cxr
    wcel
    #
    @14
    cc0
    wceq
    @13
    @1
    @2
    @16
    @0
    @1
    @2
    @11
    simpl2
    #
    @0
    @1
    @2
    @11
    simpl3
    #
    cB
    cC
    xaddcl
    #
    syl2anc
    @5
    xmul02
    syl
    cc0
    cxr
    wcel
    @15
    cc0
    wceq
    0xr
    cc0
    xaddid1
    ax-mp
    syl6eqr
    @13
    cc0
    cA
    @5
    cxmu
    @3
    @11
    simpr
    #
    oveq1d
    @13
    cc0
    @7
    cc0
    @8
    cxad
    @13
    cc0
    cB
    cxmu
    co
    #
    cc0
    @7
    @13
    @1
    @21
    cc0
    wceq
    @17
    cB
    xmul02
    syl
    @13
    cc0
    cA
    cB
    cxmu
    @20
    oveq1d
    eqtr3d
    @13
    cc0
    cC
    cxmu
    co
    #
    cc0
    @8
    @13
    @2
    @22
    cc0
    wceq
    @18
    cC
    xmul02
    syl
    @13
    cc0
    cA
    cC
    cxmu
    @20
    oveq1d
    eqtr3d
    oveq12d
    3eqtr3d
    @3
    @12
    wa
    #
    @6
    cxne
    #
    @9
    cxne
    #
    wceq
    #
    @10
    @23
    cA
    cxne
    #
    @5
    cxmu
    co
    #
    @27
    cB
    cxmu
    co
    #
    @27
    cC
    cxmu
    co
    #
    cxad
    co
    #
    @24
    @25
    @23
    @27
    cr
    wcel
    #
    @1
    @2
    cc0
    @27
    clt
    wbr
    #
    @28
    @31
    wceq
    @23
    @0
    @32
    @3
    @0
    @12
    @0
    @1
    @2
    simp1
    #
    adantr
    @0
    @27
    cA
    cneg
    cr
    cA
    rexneg
    cA
    renegcl
    eqeltrd
    syl
    @0
    @1
    @2
    @12
    simpl2
    #
    @0
    @1
    @2
    @12
    simpl3
    #
    @3
    @12
    @33
    @3
    cA
    cxr
    wcel
    #
    @12
    @33
    wb
    @3
    cA
    @34
    rexrd
    #
    cA
    xlt0neg1
    syl
    biimpa
    @27
    cB
    cC
    xadddilem
    syl31anc
    @23
    @37
    @16
    @28
    @24
    wceq
    @3
    @37
    @12
    @38
    adantr
    #
    @23
    @1
    @2
    @16
    @35
    @36
    @19
    syl2anc
    #
    cA
    @5
    xmulneg1
    syl2anc
    @23
    @31
    @7
    cxne
    #
    @8
    cxne
    #
    cxad
    co
    #
    @25
    @23
    @29
    @41
    @30
    @42
    cxad
    @23
    @37
    @1
    @29
    @41
    wceq
    @39
    @35
    cA
    cB
    xmulneg1
    syl2anc
    @23
    @37
    @2
    @30
    @42
    wceq
    @39
    @36
    cA
    cC
    xmulneg1
    syl2anc
    oveq12d
    @23
    @7
    cxr
    wcel
    #
    @8
    cxr
    wcel
    #
    @25
    @43
    wceq
    @23
    @37
    @1
    @44
    @39
    @35
    cA
    cB
    xmulcl
    syl2anc
    #
    @23
    @37
    @2
    @45
    @39
    @36
    cA
    cC
    xmulcl
    syl2anc
    #
    @7
    @8
    xnegdi
    syl2anc
    eqtr4d
    3eqtr3d
    @23
    @6
    cxr
    wcel
    #
    @9
    cxr
    wcel
    #
    @26
    @10
    wb
    @23
    @37
    @16
    @48
    @39
    @40
    cA
    @5
    xmulcl
    syl2anc
    @23
    @44
    @45
    @49
    @46
    @47
    @7
    @8
    xaddcl
    syl2anc
    @6
    @9
    xneg11
    syl2anc
    mpbid
    @3
    cc0
    cr
    wcel
    @0
    @4
    @11
    @12
    w3o
    0re
    @34
    cc0
    cA
    lttri4
    sylancr
    mpjao3dan
end
