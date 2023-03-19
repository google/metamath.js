include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cz.mm"
include "crmx.mm"
include "co.mm"
include "crmy.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "cneg.mm"
include "wo.mm"
include "cmul.mm"
include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "wi.mm"
include "acongrep.mm"
include "ad2ant2l.mm"
include "ad2ant2lr.mm"
include "w3a.mm"
include "2z.mm"
include "simpl1l.mm"
include "nnz.mm"
include "adantl.mm"
include "syl.mm"
include "zmulcl.mm"
include "sylancr.mm"
include "simplrl.mm"
include "3ad2antl1.mm"
include "simpl3l.mm"
include "elfzelz.mm"
include "simplrr.mm"
include "simpl2r.mm"
include "weq.mm"
include "wb.mm"
include "simpl2l.mm"
include "simplll.mm"
include "cn0.mm"
include "frmx.mm"
include "fovcl.mm"
include "nn0zd.mm"
include "syl2anc.mm"
include "frmy.mm"
include "jm2.26a.mm"
include "syl22anc.mm"
include "mpd.mm"
include "simpr.mm"
include "acongtr.mm"
include "syl222anc.mm"
include "simpl3r.mm"
include "acongsym.mm"
include "syl31anc.mm"
include "jm2.26lem3.mm"
include "syl121anc.mm"
include "id.mm"
include "eqidd.mm"
include "acongeq12d.mm"
include "mpbid.mm"
include "3exp1.mm"
include "expd.mm"
include "rexlimdv.mm"
include "sylanl2.mm"
include "impbid.mm"

theorem jm2.26
  let cA: class A
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vm: setvar m


  assert |- ( ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN ) /\ ( K e. ZZ /\ M e. ZZ ) ) -> ( ( ( A rmX N ) || ( ( A rmY K ) - ( A rmY M ) ) \/ ( A rmX N ) || ( ( A rmY K ) - -u ( A rmY M ) ) ) <-> ( ( 2 x. N ) || ( K - M ) \/ ( 2 x. N ) || ( K - -u M ) ) ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    wa
    #
    wa
    #
    cA
    cN
    crmx
    co
    #
    cA
    cK
    crmy
    co
    #
    cA
    cM
    crmy
    co
    #
    cmin
    co
    cdvds
    wbr
    @8
    @9
    @10
    cneg
    #
    cmin
    co
    cdvds
    wbr
    wo
    #
    c2
    cN
    cmul
    co
    #
    cK
    cM
    cmin
    co
    cdvds
    wbr
    @13
    cK
    cM
    cneg
    #
    cmin
    co
    cdvds
    wbr
    wo
    #
    @7
    @13
    vm
    cv
    #
    cM
    cmin
    co
    cdvds
    wbr
    @13
    @16
    @14
    cmin
    co
    cdvds
    wbr
    wo
    #
    vm
    cc0
    cN
    cfz
    co
    #
    wrex
    #
    @12
    @15
    wi
    #
    @2
    @5
    @19
    @1
    @4
    cN
    cM
    vm
    acongrep
    ad2ant2l
    @7
    @17
    @20
    vm
    @18
    @7
    @16
    @18
    wcel
    #
    @17
    @20
    @7
    @13
    vk
    cv
    #
    cK
    cmin
    co
    cdvds
    wbr
    @13
    @22
    cK
    cneg
    #
    cmin
    co
    cdvds
    wbr
    wo
    #
    vk
    @18
    wrex
    #
    @21
    @17
    wa
    #
    @20
    wi
    #
    @2
    @4
    @25
    @1
    @5
    cN
    cK
    vk
    acongrep
    ad2ant2lr
    @7
    @24
    @27
    vk
    @18
    @7
    @22
    @18
    wcel
    #
    @24
    @27
    @7
    @28
    @24
    wa
    #
    @26
    @12
    @15
    @7
    @29
    @26
    w3a
    #
    @12
    wa
    #
    @13
    cz
    wcel
    #
    @4
    @16
    cz
    wcel
    #
    @5
    @13
    cK
    @16
    cmin
    co
    cdvds
    wbr
    @13
    cK
    @16
    cneg
    #
    cmin
    co
    cdvds
    wbr
    wo
    #
    @17
    @15
    @31
    c2
    cz
    wcel
    cN
    cz
    wcel
    #
    @32
    2z
    @31
    @3
    @36
    @3
    @6
    @29
    @26
    @12
    simpl1l
    #
    @2
    @36
    @1
    cN
    nnz
    #
    adantl
    syl
    #
    c2
    cN
    zmulcl
    sylancr
    #
    @7
    @29
    @12
    @4
    @26
    @3
    @4
    @5
    @12
    simplrl
    3ad2antl1
    #
    @31
    @21
    @33
    @21
    @17
    @7
    @29
    @12
    simpl3l
    #
    @16
    cc0
    cN
    elfzelz
    syl
    #
    @7
    @29
    @12
    @5
    @26
    @3
    @4
    @5
    @12
    simplrr
    3ad2antl1
    #
    @31
    @32
    @33
    @4
    @13
    @16
    cK
    cmin
    co
    cdvds
    wbr
    @13
    @16
    @23
    cmin
    co
    cdvds
    wbr
    wo
    #
    @35
    @40
    @43
    @41
    @31
    @24
    @45
    @28
    @24
    @7
    @26
    @12
    simpl2r
    #
    @31
    vk
    vm
    weq
    #
    @24
    @45
    wb
    @31
    @3
    @28
    @21
    @8
    cA
    @22
    crmy
    co
    #
    cA
    @16
    crmy
    co
    #
    cmin
    co
    cdvds
    wbr
    @8
    @48
    @49
    cneg
    #
    cmin
    co
    cdvds
    wbr
    wo
    #
    @47
    @37
    @28
    @24
    @7
    @26
    @12
    simpl2l
    #
    @42
    @31
    @8
    cz
    wcel
    #
    @48
    cz
    wcel
    #
    @10
    cz
    wcel
    #
    @49
    cz
    wcel
    #
    @8
    @48
    @10
    cmin
    co
    cdvds
    wbr
    @8
    @48
    @11
    cmin
    co
    cdvds
    wbr
    wo
    #
    @8
    @10
    @49
    cmin
    co
    cdvds
    wbr
    @8
    @10
    @50
    cmin
    co
    cdvds
    wbr
    wo
    #
    @51
    @31
    @1
    @36
    @53
    @7
    @29
    @12
    @1
    @26
    @1
    @2
    @6
    @12
    simplll
    3ad2antl1
    #
    @39
    @1
    @36
    wa
    @8
    cA
    cN
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    nn0zd
    syl2anc
    #
    @31
    @1
    @22
    cz
    wcel
    #
    @54
    @59
    @31
    @28
    @61
    @52
    @22
    cc0
    cN
    elfzelz
    syl
    #
    cA
    @22
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    syl2anc
    #
    @31
    @1
    @5
    @55
    @59
    @44
    cA
    cM
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    syl2anc
    #
    @31
    @1
    @33
    @56
    @59
    @43
    cA
    @16
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    syl2anc
    @31
    @53
    @54
    @9
    cz
    wcel
    #
    @55
    @8
    @48
    @9
    cmin
    co
    cdvds
    wbr
    @8
    @48
    @9
    cneg
    cmin
    co
    cdvds
    wbr
    wo
    #
    @12
    @57
    @60
    @63
    @31
    @1
    @4
    @65
    @59
    @41
    cA
    cK
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    syl2anc
    @64
    @31
    @24
    @66
    @46
    @31
    @1
    @36
    @61
    @4
    @24
    @66
    wi
    @59
    @39
    @62
    @41
    cA
    @22
    cK
    cN
    jm2.26a
    syl22anc
    mpd
    @30
    @12
    simpr
    @8
    @48
    @9
    @10
    acongtr
    syl222anc
    @31
    @13
    cM
    @16
    cmin
    co
    cdvds
    wbr
    @13
    cM
    @34
    cmin
    co
    cdvds
    wbr
    wo
    #
    @58
    @31
    @32
    @33
    @5
    @17
    @67
    @40
    @43
    @44
    @21
    @17
    @7
    @29
    @12
    simpl3r
    #
    @13
    @16
    cM
    acongsym
    syl31anc
    @31
    @1
    @36
    @5
    @33
    @67
    @58
    wi
    @59
    @39
    @44
    @43
    cA
    cM
    @16
    cN
    jm2.26a
    syl22anc
    mpd
    @8
    @48
    @10
    @49
    acongtr
    syl222anc
    cA
    @22
    @16
    cN
    jm2.26lem3
    syl121anc
    @47
    @13
    @22
    @16
    cK
    cK
    @47
    id
    @47
    cK
    eqidd
    acongeq12d
    syl
    mpbid
    @13
    @16
    cK
    acongsym
    syl31anc
    @68
    @13
    cK
    @16
    cM
    acongtr
    syl222anc
    3exp1
    expd
    rexlimdv
    mpd
    expd
    rexlimdv
    mpd
    @2
    @1
    @36
    @6
    @15
    @12
    wi
    @38
    cA
    cK
    cM
    cN
    jm2.26a
    sylanl2
    impbid
end
