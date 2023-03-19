include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wceq.mm"
include "cxne.mm"
include "cxad.mm"
include "wa.mm"
include "cxr.mm"
include "iccssxr.mm"
include "simpl1.mm"
include "sseldi.mm"
include "simpr.mm"
include "simpl3.mm"
include "eqbrtrrd.mm"
include "xgepnf.mm"
include "biimpa.mm"
include "syl2anc.mm"
include "xnegeq.mm"
include "syl.mm"
include "oveq12d.mm"
include "pnfxr.mm"
include "xnegid.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "xaddid2.mm"
include "mp1i.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "wn.mm"
include "cmnf.mm"
include "wne.mm"
include "xrge0neqmnf.mm"
include "simpl2.mm"
include "xnegcld.mm"
include "xnegneg.mm"
include "sylan9req.mm"
include "xnegmnf.mm"
include "stoic1a.mm"
include "neqned.mm"
include "xaddass.mm"
include "syl222anc.mm"
include "xnegcl.mm"
include "xaddcom.mm"
include "mpancom.mm"
include "eqtrd.mm"
include "xaddid1.mm"
include "sylan9eqr.mm"
include "pm2.61dan.mm"

theorem xrge0npcan
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ( 0 [,] +oo ) /\ B e. ( 0 [,] +oo ) /\ B <_ A ) -> ( ( A +e -e B ) +e B ) = A )

  proof
    cA
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cB
    cA
    cle
    wbr
    #
    w3a
    #
    cB
    cpnf
    wceq
    #
    cA
    cB
    cxne
    #
    cxad
    co
    #
    cB
    cxad
    co
    #
    cA
    wceq
    @4
    @5
    wa
    #
    @8
    cpnf
    cA
    @9
    @8
    cc0
    cB
    cxad
    co
    cc0
    cpnf
    cxad
    co
    #
    cpnf
    @9
    @7
    cc0
    cB
    cxad
    @9
    @7
    cpnf
    cpnf
    cxne
    #
    cxad
    co
    #
    cc0
    @9
    cA
    cpnf
    @6
    @11
    cxad
    @9
    cA
    cxr
    wcel
    #
    cpnf
    cA
    cle
    wbr
    #
    cA
    cpnf
    wceq
    #
    @9
    @0
    cxr
    cA
    cc0
    cpnf
    iccssxr
    #
    @1
    @2
    @3
    @5
    simpl1
    sseldi
    @9
    cB
    cpnf
    cA
    cle
    @4
    @5
    simpr
    #
    @1
    @2
    @3
    @5
    simpl3
    eqbrtrrd
    @13
    @14
    @15
    cA
    xgepnf
    biimpa
    syl2anc
    #
    @9
    @5
    @6
    @11
    wceq
    @17
    cB
    cpnf
    xnegeq
    syl
    oveq12d
    cpnf
    cxr
    wcel
    #
    @12
    cc0
    wceq
    pnfxr
    cpnf
    xnegid
    ax-mp
    syl6eq
    oveq1d
    @9
    cB
    cpnf
    cc0
    cxad
    @17
    oveq2d
    @19
    @10
    cpnf
    wceq
    @9
    pnfxr
    cpnf
    xaddid2
    mp1i
    3eqtrd
    @18
    eqtr4d
    @4
    @5
    wn
    #
    wa
    #
    @8
    cA
    @6
    cB
    cxad
    co
    #
    cxad
    co
    #
    cA
    @21
    @13
    cA
    cmnf
    wne
    #
    @6
    cxr
    wcel
    #
    @6
    cmnf
    wne
    #
    cB
    cxr
    wcel
    #
    cB
    cmnf
    wne
    #
    @8
    @23
    wceq
    @21
    @0
    cxr
    cA
    @16
    @1
    @2
    @3
    @20
    simpl1
    #
    sseldi
    #
    @21
    @1
    @24
    @29
    cA
    xrge0neqmnf
    syl
    @21
    cB
    @21
    @0
    cxr
    cB
    @16
    @1
    @2
    @3
    @20
    simpl2
    #
    sseldi
    #
    xnegcld
    @21
    @27
    @20
    @26
    @32
    @4
    @20
    simpr
    @27
    @20
    wa
    @6
    cmnf
    @27
    @6
    cmnf
    wceq
    #
    @5
    @27
    @33
    wa
    cB
    cmnf
    cxne
    #
    cpnf
    @27
    @33
    cB
    @6
    cxne
    @34
    cB
    xnegneg
    @6
    cmnf
    xnegeq
    sylan9req
    xnegmnf
    syl6eq
    stoic1a
    neqned
    syl2anc
    @32
    @21
    @2
    @28
    @31
    cB
    xrge0neqmnf
    syl
    cA
    @6
    cB
    xaddass
    syl222anc
    @21
    @13
    @27
    @23
    cA
    wceq
    @30
    @32
    @27
    @13
    @23
    cA
    cc0
    cxad
    co
    cA
    @27
    @22
    cc0
    cA
    cxad
    @27
    @22
    cB
    @6
    cxad
    co
    #
    cc0
    @25
    @27
    @22
    @35
    wceq
    cB
    xnegcl
    @6
    cB
    xaddcom
    mpancom
    cB
    xnegid
    eqtrd
    oveq2d
    cA
    xaddid1
    sylan9eqr
    syl2anc
    eqtrd
    pm2.61dan
end
