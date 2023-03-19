include "cc.mm"
include "wcel.mm"
include "cply.mm"
include "cfv.mm"
include "wa.mm"
include "cn0.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "ccoe.mm"
include "wf.mm"
include "wfn.mm"
include "wss.mm"
include "ssid.mm"
include "plyconst.mm"
include "mpan.mm"
include "plyssc.mm"
include "sseli.mm"
include "plymulcl.mm"
include "syl2an.mm"
include "eqid.mm"
include "coef3.mm"
include "ffn.mm"
include "3syl.mm"
include "cvv.mm"
include "fconstg.mm"
include "adantr.mm"
include "syl.mm"
include "adantl.mm"
include "nn0ex.mm"
include "a1i.mm"
include "inidm.mm"
include "offn.mm"
include "cv.mm"
include "cc0.mm"
include "cmin.mm"
include "wceq.mm"
include "ad2antrr.mm"
include "coefv0.mm"
include "simpll.mm"
include "0cn.mm"
include "fvconst2g.mm"
include "sylancl.mm"
include "eqtr3d.mm"
include "simpr.mm"
include "nn0cnd.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cfz.mm"
include "csu.mm"
include "ad2antlr.mm"
include "coemul.mm"
include "syl3anc.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "fzss2.mm"
include "elfz1eq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "ffvelrnda.mm"
include "mulcld.mm"
include "eqeltrd.mm"
include "cdif.mm"
include "wn.mm"
include "eldifn.mm"
include "wne.mm"
include "cdgr.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "eldifi.mm"
include "elfznn0.mm"
include "dgrub.mm"
include "3expia.mm"
include "0dgr.mm"
include "ad3antrrr.mm"
include "breq2d.mm"
include "wb.mm"
include "nn0le0eq0.mm"
include "bitrd.mm"
include "sylibd.mm"
include "id.mm"
include "cz.mm"
include "0z.mm"
include "elfz3.mm"
include "ax-mp.mm"
include "syl6eqel.mm"
include "syl6.mm"
include "necon1bd.mm"
include "mpd.mm"
include "oveq1d.mm"
include "fznn0sub.mm"
include "ffvelrn.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "fzfid.mm"
include "fsumss.mm"
include "fsum1.mm"
include "sylancr.mm"
include "3eqtr2d.mm"
include "simpl.mm"
include "eqidd.mm"
include "ofc1.mm"
include "3eqtr4d.mm"
include "eqfnfvd.mm"

theorem coemulc
  let cA: class A
  let cS: class S
  let cF: class F
  let vk: setvar k
  let vn: setvar n


  assert |- ( ( A e. CC /\ F e. ( Poly ` S ) ) -> ( coeff ` ( ( CC X. { A } ) oF x. F ) ) = ( ( NN0 X. { A } ) oF x. ( coeff ` F ) ) )

  proof
    cA
    cc
    wcel
    #
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    wa
    #
    vn
    cn0
    cc
    cA
    csn
    #
    cxp
    #
    cF
    cmul
    cof
    #
    co
    #
    ccoe
    cfv
    #
    cn0
    @4
    cxp
    #
    cF
    ccoe
    cfv
    #
    @6
    co
    #
    @3
    @7
    cc
    cply
    cfv
    #
    wcel
    #
    cn0
    cc
    @8
    wf
    @8
    cn0
    wfn
    @0
    @5
    @12
    wcel
    #
    cF
    @12
    wcel
    #
    @13
    @2
    cc
    cc
    wss
    @0
    @14
    cc
    ssid
    cA
    cc
    plyconst
    mpan
    #
    @1
    @12
    cF
    cS
    plyssc
    sseli
    #
    cc
    @5
    cF
    plymulcl
    syl2an
    @8
    cc
    @7
    @8
    eqid
    coef3
    cn0
    cc
    @8
    ffn
    3syl
    @3
    cn0
    cn0
    cmul
    cn0
    @9
    @10
    cvv
    cvv
    @3
    cn0
    @4
    @9
    wf
    #
    @9
    cn0
    wfn
    @0
    @18
    @2
    cn0
    cA
    cc
    fconstg
    adantr
    cn0
    @4
    @9
    ffn
    syl
    @3
    cn0
    cc
    @10
    wf
    #
    @10
    cn0
    wfn
    @2
    @19
    @0
    @10
    cS
    cF
    @10
    eqid
    #
    coef3
    adantl
    #
    cn0
    cc
    @10
    ffn
    syl
    #
    cn0
    cvv
    wcel
    @3
    nn0ex
    a1i
    #
    @23
    cn0
    inidm
    offn
    @3
    vn
    cv
    #
    cn0
    wcel
    #
    wa
    #
    cc0
    @5
    ccoe
    cfv
    #
    cfv
    #
    @24
    cc0
    cmin
    co
    #
    @10
    cfv
    #
    cmul
    co
    #
    cA
    @24
    @10
    cfv
    #
    cmul
    co
    #
    @24
    @8
    cfv
    #
    @24
    @11
    cfv
    @26
    @28
    cA
    @30
    @32
    cmul
    @26
    cc0
    @5
    cfv
    #
    @28
    cA
    @26
    @14
    @35
    @28
    wceq
    @0
    @14
    @2
    @25
    @16
    ad2antrr
    #
    @27
    cc
    @5
    @27
    eqid
    #
    coefv0
    syl
    @26
    @0
    cc0
    cc
    wcel
    @35
    cA
    wceq
    @0
    @2
    @25
    simpll
    #
    0cn
    cc
    cA
    cc0
    cc
    fvconst2g
    sylancl
    eqtr3d
    @26
    @29
    @24
    @10
    @26
    @24
    @26
    @24
    @3
    @25
    simpr
    #
    nn0cnd
    subid1d
    fveq2d
    oveq12d
    #
    @26
    @34
    cc0
    @24
    cfz
    co
    #
    vk
    cv
    #
    @27
    cfv
    #
    @24
    @42
    cmin
    co
    #
    @10
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    cc0
    cc0
    cfz
    co
    #
    @46
    vk
    csu
    #
    @31
    @26
    @14
    @15
    @25
    @34
    @47
    wceq
    @36
    @2
    @15
    @0
    @25
    @17
    ad2antlr
    @39
    @27
    @10
    cc
    vk
    @5
    cF
    @24
    @37
    @20
    coemul
    syl3anc
    @26
    @48
    @41
    @46
    vk
    @26
    @24
    cc0
    cuz
    cfv
    #
    wcel
    @48
    @41
    wss
    @26
    @24
    cn0
    @50
    @39
    nn0uz
    syl6eleq
    cc0
    cc0
    @24
    fzss2
    syl
    @26
    @42
    @48
    wcel
    #
    wa
    #
    @46
    @31
    cc
    @52
    @42
    cc0
    wceq
    #
    @46
    @31
    wceq
    @51
    @53
    @26
    @42
    cc0
    elfz1eq
    adantl
    @53
    @43
    @28
    @45
    @30
    cmul
    @42
    cc0
    @27
    fveq2
    @53
    @44
    @29
    @10
    @42
    cc0
    @24
    cmin
    oveq2
    fveq2d
    oveq12d
    #
    syl
    @26
    @31
    cc
    wcel
    #
    @51
    @26
    @31
    @33
    cc
    @40
    @26
    cA
    @32
    @38
    @3
    cn0
    cc
    @24
    @10
    @21
    ffvelrnda
    mulcld
    eqeltrd
    #
    adantr
    eqeltrd
    @26
    @42
    @41
    @48
    cdif
    wcel
    #
    wa
    #
    @46
    cc0
    @45
    cmul
    co
    cc0
    @58
    @43
    cc0
    @45
    cmul
    @58
    @51
    wn
    #
    @43
    cc0
    wceq
    @57
    @59
    @26
    @42
    @41
    @48
    eldifn
    adantl
    @58
    @51
    @43
    cc0
    @58
    @43
    cc0
    wne
    #
    @53
    @51
    @58
    @60
    @42
    @5
    cdgr
    cfv
    #
    cle
    wbr
    #
    @53
    @26
    @14
    @42
    cn0
    wcel
    #
    @60
    @62
    wi
    @57
    @36
    @57
    @42
    @41
    wcel
    #
    @63
    @42
    @41
    @48
    eldifi
    #
    @42
    @24
    elfznn0
    syl
    #
    @14
    @63
    @60
    @62
    @27
    cc
    @5
    @42
    @61
    @37
    @61
    eqid
    dgrub
    3expia
    syl2an
    @58
    @62
    @42
    cc0
    cle
    wbr
    #
    @53
    @58
    @61
    cc0
    @42
    cle
    @0
    @61
    cc0
    wceq
    @2
    @25
    @57
    cA
    0dgr
    ad3antrrr
    breq2d
    @58
    @63
    @67
    @53
    wb
    @57
    @63
    @26
    @66
    adantl
    @42
    nn0le0eq0
    syl
    bitrd
    sylibd
    @53
    @42
    cc0
    @48
    @53
    id
    cc0
    cz
    wcel
    #
    cc0
    @48
    wcel
    0z
    cc0
    elfz3
    ax-mp
    syl6eqel
    syl6
    necon1bd
    mpd
    oveq1d
    @58
    @45
    @26
    @19
    @44
    cn0
    wcel
    #
    @45
    cc
    wcel
    @57
    @3
    @19
    @25
    @21
    adantr
    @57
    @64
    @69
    @65
    @42
    cc0
    @24
    fznn0sub
    syl
    cn0
    cc
    @44
    @10
    ffvelrn
    syl2an
    mul02d
    eqtrd
    @26
    cc0
    @24
    fzfid
    fsumss
    @26
    @68
    @55
    @49
    @31
    wceq
    0z
    @56
    @46
    @31
    vk
    cc0
    @54
    fsum1
    sylancr
    3eqtr2d
    @3
    cn0
    cA
    @32
    cmul
    @10
    cvv
    cc
    @24
    @23
    @0
    @2
    simpl
    @22
    @26
    @32
    eqidd
    ofc1
    3eqtr4d
    eqfnfvd
end
