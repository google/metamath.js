include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cioo.mm"
include "co.mm"
include "covol.mm"
include "cfv.mm"
include "cvol.mm"
include "cmin.mm"
include "cdm.mm"
include "wceq.mm"
include "ioombl.mm"
include "mblvol.mm"
include "ax-mp.mm"
include "cicc.mm"
include "wa.mm"
include "iccmbl.mm"
include "syl.mm"
include "3adant3.mm"
include "cpr.mm"
include "cun.mm"
include "caddc.mm"
include "cin.mm"
include "c0.mm"
include "a1i.mm"
include "wss.mm"
include "cc0.mm"
include "prssi.mm"
include "cfn.mm"
include "prfi.mm"
include "ovolfi.mm"
include "sylancr.mm"
include "nulmbl.mm"
include "syl2anc.mm"
include "csn.mm"
include "df-pr.mm"
include "ineq2i.mm"
include "indi.mm"
include "eqtri.mm"
include "wn.mm"
include "clt.mm"
include "simp1.mm"
include "ltnrd.mm"
include "eliooord.mm"
include "simpld.mm"
include "nsyl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "simp2.mm"
include "simprd.mm"
include "uneq12d.mm"
include "un0.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "ioossicc.mm"
include "iccssre.mm"
include "ovolicc.mm"
include "resubcld.mm"
include "eqeltrd.mm"
include "ovolsscl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "eqtrd.mm"
include "0re.mm"
include "syl6eqel.mm"
include "volun.mm"
include "syl32anc.mm"
include "cxr.mm"
include "rexr.mm"
include "id.mm"
include "prunioo.mm"
include "syl3an.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "recnd.mm"
include "addid1d.mm"
include "3eqtr3d.mm"
include "syl5eqr.mm"

theorem ovolioo
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> ( vol* ` ( A (,) B ) ) = ( B - A ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    #
    cA
    cB
    cioo
    co
    #
    covol
    cfv
    #
    @4
    cvol
    cfv
    #
    cB
    cA
    cmin
    co
    #
    @4
    cvol
    cdm
    #
    wcel
    #
    @6
    @5
    wceq
    cA
    cB
    ioombl
    #
    @4
    mblvol
    ax-mp
    #
    @3
    cA
    cB
    cicc
    co
    #
    cvol
    cfv
    #
    @12
    covol
    cfv
    #
    @6
    @7
    @0
    @1
    @13
    @14
    wceq
    #
    @2
    @0
    @1
    wa
    @12
    @8
    wcel
    @15
    cA
    cB
    iccmbl
    @12
    mblvol
    syl
    3adant3
    @3
    @4
    cA
    cB
    cpr
    #
    cun
    #
    cvol
    cfv
    #
    @6
    @16
    cvol
    cfv
    #
    caddc
    co
    #
    @13
    @6
    @3
    @9
    @16
    @8
    wcel
    #
    @4
    @16
    cin
    #
    c0
    wceq
    @6
    cr
    wcel
    @19
    cr
    wcel
    @18
    @20
    wceq
    @9
    @3
    @10
    a1i
    @3
    @16
    cr
    wss
    #
    @16
    covol
    cfv
    #
    cc0
    wceq
    #
    @21
    @0
    @1
    @23
    @2
    cA
    cB
    cr
    prssi
    3adant3
    #
    @3
    @16
    cfn
    wcel
    @23
    @25
    cA
    cB
    prfi
    @26
    @16
    ovolfi
    sylancr
    #
    @16
    nulmbl
    syl2anc
    #
    @3
    @22
    @4
    cA
    csn
    #
    cin
    #
    @4
    cB
    csn
    #
    cin
    #
    cun
    #
    c0
    @22
    @4
    @29
    @31
    cun
    #
    cin
    @33
    @16
    @34
    @4
    cA
    cB
    df-pr
    ineq2i
    @4
    @29
    @31
    indi
    eqtri
    @3
    @33
    c0
    c0
    cun
    c0
    @3
    @30
    c0
    @32
    c0
    @3
    cA
    @4
    wcel
    #
    wn
    @30
    c0
    wceq
    @3
    cA
    cA
    clt
    wbr
    #
    @35
    @3
    cA
    @0
    @1
    @2
    simp1
    #
    ltnrd
    @35
    @36
    cA
    cB
    clt
    wbr
    #
    cA
    cA
    cB
    eliooord
    simpld
    nsyl
    @4
    cA
    disjsn
    sylibr
    @3
    cB
    @4
    wcel
    #
    wn
    @32
    c0
    wceq
    @3
    cB
    cB
    clt
    wbr
    #
    @39
    @3
    cB
    @0
    @1
    @2
    simp2
    #
    ltnrd
    @39
    @38
    @40
    cB
    cA
    cB
    eliooord
    simprd
    nsyl
    @4
    cB
    disjsn
    sylibr
    uneq12d
    c0
    un0
    syl6eq
    syl5eq
    @3
    @6
    @5
    cr
    @11
    @3
    @4
    @12
    wss
    #
    @12
    cr
    wss
    #
    @14
    cr
    wcel
    @5
    cr
    wcel
    @42
    @3
    cA
    cB
    ioossicc
    a1i
    @0
    @1
    @43
    @2
    cA
    cB
    iccssre
    3adant3
    @3
    @14
    @7
    cr
    cA
    cB
    ovolicc
    #
    @3
    cB
    cA
    @41
    @37
    resubcld
    eqeltrd
    @4
    @12
    ovolsscl
    syl3anc
    syl5eqel
    #
    @3
    @19
    cc0
    cr
    @3
    @19
    @24
    cc0
    @3
    @21
    @19
    @24
    wceq
    @28
    @16
    mblvol
    syl
    @27
    eqtrd
    #
    0re
    syl6eqel
    @4
    @16
    volun
    syl32anc
    @3
    @17
    @12
    cvol
    @0
    cA
    cxr
    wcel
    @1
    cB
    cxr
    wcel
    @2
    @2
    @17
    @12
    wceq
    cA
    rexr
    cB
    rexr
    @2
    id
    cA
    cB
    prunioo
    syl3an
    fveq2d
    @3
    @20
    @6
    cc0
    caddc
    co
    @6
    @3
    @19
    cc0
    @6
    caddc
    @46
    oveq2d
    @3
    @6
    @3
    @6
    @45
    recnd
    addid1d
    eqtrd
    3eqtr3d
    @44
    3eqtr3d
    syl5eqr
end
