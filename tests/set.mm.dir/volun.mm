include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "cfv.mm"
include "cr.mm"
include "wa.mm"
include "cun.mm"
include "caddc.mm"
include "co.mm"
include "covol.mm"
include "cdif.mm"
include "wss.mm"
include "simpl1.mm"
include "mblss.mm"
include "syl.mm"
include "simpl2.mm"
include "unssd.mm"
include "cle.mm"
include "wbr.mm"
include "readdcl.mm"
include "adantl.mm"
include "simprl.mm"
include "simprr.mm"
include "ovolun.mm"
include "syl22anc.mm"
include "ovollecl.mm"
include "syl3anc.mm"
include "mblsplit.mm"
include "simpl3.mm"
include "indir.mm"
include "inidm.mm"
include "incom.mm"
include "uneq12i.mm"
include "unabs.mm"
include "eqtri.mm"
include "a1i.mm"
include "fveq2d.mm"
include "eqeq1i.mm"
include "disj3.mm"
include "bitr3i.mm"
include "biimpi.mm"
include "uncom.mm"
include "difeq1i.mm"
include "difun2.mm"
include "syl6reqr.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "ex.mm"
include "wb.mm"
include "mblvol.mm"
include "eleq1d.mm"
include "bi2anan9.mm"
include "3adant3.mm"
include "unmbl.mm"
include "oveqan12d.mm"
include "eqeq12d.mm"
include "3imtr4d.mm"
include "imp.mm"

theorem volun
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. dom vol /\ B e. dom vol /\ ( A i^i B ) = (/) ) /\ ( ( vol ` A ) e. RR /\ ( vol ` B ) e. RR ) ) -> ( vol ` ( A u. B ) ) = ( ( vol ` A ) + ( vol ` B ) ) )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cA
    cB
    cin
    #
    c0
    wceq
    #
    w3a
    #
    cA
    cvol
    cfv
    #
    cr
    wcel
    #
    cB
    cvol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    cA
    cB
    cun
    #
    cvol
    cfv
    #
    @6
    @8
    caddc
    co
    #
    wceq
    #
    @5
    cA
    covol
    cfv
    #
    cr
    wcel
    #
    cB
    covol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    @11
    covol
    cfv
    #
    @15
    @17
    caddc
    co
    #
    wceq
    #
    @10
    @14
    @5
    @19
    @22
    @5
    @19
    wa
    #
    @20
    @11
    cA
    cin
    #
    covol
    cfv
    #
    @11
    cA
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    @21
    @23
    @1
    @11
    cr
    wss
    #
    @20
    cr
    wcel
    #
    @20
    @28
    wceq
    @1
    @2
    @4
    @19
    simpl1
    #
    @23
    cA
    cB
    cr
    @23
    @1
    cA
    cr
    wss
    #
    @31
    cA
    mblss
    syl
    #
    @23
    @2
    cB
    cr
    wss
    #
    @1
    @2
    @4
    @19
    simpl2
    cB
    mblss
    syl
    #
    unssd
    #
    @23
    @29
    @21
    cr
    wcel
    #
    @20
    @21
    cle
    wbr
    #
    @30
    @36
    @19
    @37
    @5
    @15
    @17
    readdcl
    adantl
    @23
    @32
    @16
    @34
    @18
    @38
    @33
    @5
    @16
    @18
    simprl
    @35
    @5
    @16
    @18
    simprr
    cA
    cB
    ovolun
    syl22anc
    @11
    @21
    ovollecl
    syl3anc
    cA
    @11
    mblsplit
    syl3anc
    @23
    @4
    @28
    @21
    wceq
    @1
    @2
    @4
    @19
    simpl3
    @4
    @25
    @15
    @27
    @17
    caddc
    @4
    @24
    cA
    covol
    @24
    cA
    wceq
    @4
    @24
    cA
    cA
    cin
    #
    cB
    cA
    cin
    #
    cun
    #
    cA
    cA
    cB
    cA
    indir
    @41
    cA
    @3
    cun
    cA
    @39
    cA
    @40
    @3
    cA
    inidm
    cB
    cA
    incom
    #
    uneq12i
    cA
    cB
    unabs
    eqtri
    eqtri
    a1i
    fveq2d
    @4
    @26
    cB
    covol
    @4
    cB
    cB
    cA
    cdif
    #
    @26
    @4
    cB
    @43
    wceq
    #
    @4
    @40
    c0
    wceq
    @44
    @40
    @3
    c0
    @42
    eqeq1i
    cB
    cA
    disj3
    bitr3i
    biimpi
    @26
    cB
    cA
    cun
    #
    cA
    cdif
    @43
    @11
    @45
    cA
    cA
    cB
    uncom
    difeq1i
    cB
    cA
    difun2
    eqtri
    syl6reqr
    fveq2d
    oveq12d
    syl
    eqtrd
    ex
    @1
    @2
    @10
    @19
    wb
    @4
    @1
    @7
    @16
    @2
    @9
    @18
    @1
    @6
    @15
    cr
    cA
    mblvol
    #
    eleq1d
    @2
    @8
    @17
    cr
    cB
    mblvol
    #
    eleq1d
    bi2anan9
    3adant3
    @1
    @2
    @14
    @22
    wb
    @4
    @1
    @2
    wa
    #
    @12
    @20
    @13
    @21
    @48
    @11
    @0
    wcel
    @12
    @20
    wceq
    cA
    cB
    unmbl
    @11
    mblvol
    syl
    @1
    @2
    @6
    @15
    @8
    @17
    caddc
    @46
    @47
    oveqan12d
    eqeq12d
    3adant3
    3imtr4d
    imp
end
