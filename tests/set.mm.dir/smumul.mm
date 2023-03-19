include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cbits.mm"
include "cfv.mm"
include "csmu.mm"
include "co.mm"
include "cmul.mm"
include "cv.mm"
include "cn0.mm"
include "wi.mm"
include "wss.mm"
include "bitsss.mm"
include "smucl.mm"
include "mp2an.mm"
include "sseli.mm"
include "a1i.mm"
include "wb.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "cfzo.mm"
include "cin.mm"
include "c2.mm"
include "cexp.mm"
include "cmo.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "1nn0.mm"
include "nn0addcld.mm"
include "smumullem.mm"
include "ineq1d.mm"
include "wceq.mm"
include "cn.mm"
include "2nn.mm"
include "nnexpcld.mm"
include "zmodcld.mm"
include "nn0zd.mm"
include "zmulcld.mm"
include "bitsmod.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "inass.mm"
include "inidm.mm"
include "ineq2i.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "ineq1i.mm"
include "inss1.mm"
include "syl5ss.mm"
include "smueq.mm"
include "3eqtr4a.mm"
include "nnrpd.mm"
include "cr.mm"
include "crp.mm"
include "zred.mm"
include "modabs2.mm"
include "eqidd.mm"
include "modmul12d.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "elin.mm"
include "3bitr3g.mm"
include "cfz.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz2b.mm"
include "sylib.mm"
include "fzval3.mm"
include "syl.mm"
include "eleqtrd.mm"
include "biantrud.mm"
include "3bitr4d.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "eqrdv.mm"

theorem smumul
  let cA: class A
  let cB: class B
  let vk: setvar k


  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> ( ( bits ` A ) smul ( bits ` B ) ) = ( bits ` ( A x. B ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    vk
    cA
    cbits
    cfv
    #
    cB
    cbits
    cfv
    #
    csmu
    co
    #
    cA
    cB
    cmul
    co
    #
    cbits
    cfv
    #
    @2
    vk
    cv
    #
    cn0
    wcel
    #
    @8
    @5
    wcel
    #
    @8
    @7
    wcel
    #
    @10
    @9
    wi
    @2
    @5
    cn0
    @8
    @3
    cn0
    wss
    #
    @4
    cn0
    wss
    #
    @5
    cn0
    wss
    cA
    bitsss
    #
    cB
    bitsss
    #
    @3
    @4
    smucl
    mp2an
    sseli
    a1i
    @11
    @9
    wi
    @2
    @7
    cn0
    @8
    @6
    bitsss
    sseli
    a1i
    @2
    @9
    @10
    @11
    wb
    @2
    @9
    wa
    #
    @10
    @8
    cc0
    @8
    c1
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    wa
    #
    @11
    @19
    wa
    #
    @10
    @11
    @16
    @8
    @5
    @18
    cin
    #
    wcel
    @8
    @7
    @18
    cin
    #
    wcel
    @20
    @21
    @16
    @22
    @23
    @8
    @16
    @22
    @6
    c2
    @17
    cexp
    co
    #
    cmo
    co
    #
    cbits
    cfv
    #
    @23
    @16
    @3
    @18
    cin
    #
    @4
    csmu
    co
    #
    @18
    cin
    #
    cA
    @24
    cmo
    co
    #
    cB
    cmul
    co
    #
    @24
    cmo
    co
    #
    cbits
    cfv
    #
    @22
    @26
    @16
    @29
    @31
    cbits
    cfv
    #
    @18
    cin
    #
    @33
    @16
    @28
    @34
    @18
    @16
    cA
    cB
    @17
    @0
    @1
    @9
    simpll
    #
    @0
    @1
    @9
    simplr
    #
    @16
    @8
    c1
    @2
    @9
    simpr
    #
    c1
    cn0
    wcel
    @16
    1nn0
    a1i
    nn0addcld
    #
    smumullem
    ineq1d
    @16
    @31
    cz
    wcel
    @17
    cn0
    wcel
    #
    @33
    @35
    wceq
    @16
    @30
    cB
    @16
    @30
    @16
    cA
    @24
    @36
    @16
    c2
    @17
    c2
    cn
    wcel
    @16
    2nn
    a1i
    @39
    nnexpcld
    #
    zmodcld
    nn0zd
    #
    @37
    zmulcld
    @39
    @17
    @31
    bitsmod
    syl2anc
    eqtr4d
    @16
    @27
    @18
    cin
    #
    @4
    @18
    cin
    #
    csmu
    co
    #
    @18
    cin
    @27
    @44
    csmu
    co
    #
    @18
    cin
    @29
    @22
    @45
    @46
    @18
    @43
    @27
    @44
    csmu
    @43
    @3
    @18
    @18
    cin
    #
    cin
    @27
    @3
    @18
    @18
    inass
    @47
    @18
    @3
    @18
    inidm
    ineq2i
    eqtri
    oveq1i
    ineq1i
    @16
    @27
    @4
    @17
    @16
    @27
    @3
    cn0
    @3
    @18
    inss1
    @12
    @16
    @14
    a1i
    #
    syl5ss
    @13
    @16
    @15
    a1i
    #
    @39
    smueq
    @16
    @3
    @4
    @17
    @48
    @49
    @39
    smueq
    3eqtr4a
    @16
    @32
    @25
    cbits
    @16
    @30
    cA
    cB
    cB
    @24
    @42
    @36
    @37
    @37
    @16
    @24
    @41
    nnrpd
    #
    @16
    cA
    cr
    wcel
    @24
    crp
    wcel
    @30
    @24
    cmo
    co
    @30
    wceq
    @16
    cA
    @36
    zred
    @50
    cA
    @24
    modabs2
    syl2anc
    @16
    cB
    @24
    cmo
    co
    eqidd
    modmul12d
    fveq2d
    3eqtr3d
    @16
    @6
    cz
    wcel
    @40
    @26
    @23
    wceq
    @16
    cA
    cB
    @36
    @37
    zmulcld
    @39
    @17
    @6
    bitsmod
    syl2anc
    eqtrd
    eleq2d
    @8
    @5
    @18
    elin
    @8
    @7
    @18
    elin
    3bitr3g
    @16
    @19
    @10
    @16
    @8
    cc0
    @8
    cfz
    co
    #
    @18
    @16
    @8
    cc0
    cuz
    cfv
    #
    wcel
    @8
    @51
    wcel
    @16
    @8
    cn0
    @52
    @38
    nn0uz
    syl6eleq
    cc0
    @8
    eluzfz2b
    sylib
    @16
    @8
    cz
    wcel
    @51
    @18
    wceq
    @16
    @8
    @38
    nn0zd
    cc0
    @8
    fzval3
    syl
    eleqtrd
    #
    biantrud
    @16
    @19
    @11
    @53
    biantrud
    3bitr4d
    ex
    pm5.21ndd
    eqrdv
end
