include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cioo.mm"
include "cv.mm"
include "wrex.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "cr.mm"
include "csup.mm"
include "ssrab2.mm"
include "wor.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "ltso.mm"
include "a1i.mm"
include "fzofi.mm"
include "ssfi.mm"
include "mp2an.mm"
include "cz.mm"
include "0zd.mm"
include "nnzd.mm"
include "nngt0d.mm"
include "fzolb.mm"
include "syl3anbrc.mm"
include "cfz.mm"
include "elfzofz.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "cicc.mm"
include "cuz.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "iccssred.mm"
include "sseldd.mm"
include "cxr.mm"
include "cle.mm"
include "rexrd.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "wceq.mm"
include "crn.mm"
include "wa.mm"
include "simpr.mm"
include "wfn.mm"
include "wf.mm"
include "ffn.mm"
include "adantr.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "mtand.mm"
include "neqned.mm"
include "leneltd.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "fzossfz.mm"
include "fzssz.mm"
include "zssre.mm"
include "sstri.mm"
include "fisupcl.mm"
include "syl13anc.mm"
include "sseldi.mm"
include "syl5eqel.mm"
include "fzofzp1.mm"
include "sylib.mm"
include "simprd.mm"
include "wn.mm"
include "wo.mm"
include "ltp1.mm"
include "id.mm"
include "peano2re.mm"
include "ltnled.mm"
include "mpbid.mm"
include "wral.mm"
include "elrabi.mm"
include "elfzo0le.mm"
include "adantl.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "elfzuz.mm"
include "zred.mm"
include "elfzle2.mm"
include "iccleub.mm"
include "breqtrd.mm"
include "adantlr.mm"
include "elfzo2.mm"
include "suprzub.mm"
include "syl6breqr.mm"
include "eqcom.mm"
include "biimpi.mm"
include "jca.mm"
include "pm4.56.mm"
include "leloed.mm"
include "mtbird.mm"
include "mpbird.mm"
include "eliood.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "eleq2d.mm"

theorem fourierdlem25
  let wph: wff ph
  let cC: class C
  let cQ: class Q
  let vj: setvar j
  let vk: setvar k
  let cI: class I
  let cM: class M
  let vh: setvar h
  let vm: setvar m
  let vx: setvar x
  assume fourierdlem25.m: |- ( ph -> M e. NN )
  assume fourierdlem25.qf: |- ( ph -> Q : ( 0 ... M ) --> RR )
  assume fourierdlem25.cel: |- ( ph -> C e. ( ( Q ` 0 ) [,] ( Q ` M ) ) )
  assume fourierdlem25.cnel: |- ( ph -> -. C e. ran Q )
  assume fourierdlem25.i: |- I = sup ( { k e. ( 0 ..^ M ) | ( Q ` k ) < C } , RR , < )

  disjoint C k
  disjoint C j
  disjoint I j
  disjoint I k
  disjoint M k
  disjoint M j
  disjoint Q k
  disjoint Q j
  disjoint C h
  disjoint C m
  disjoint h k
  disjoint h m
  disjoint k m
  disjoint I m
  disjoint M h
  disjoint M m
  disjoint Q h
  disjoint Q m
  disjoint h ph
  disjoint k x
  assert |- ( ph -> E. j e. ( 0 ..^ M ) C e. ( ( Q ` j ) (,) ( Q ` ( j + 1 ) ) ) )

  proof
    wph
    cI
    cc0
    cM
    cfzo
    co
    #
    wcel
    #
    cC
    cI
    cQ
    cfv
    #
    cI
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cioo
    co
    #
    wcel
    #
    cC
    vj
    cv
    #
    cQ
    cfv
    #
    @7
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cioo
    co
    #
    wcel
    #
    vj
    @0
    wrex
    wph
    cI
    vk
    cv
    #
    cQ
    cfv
    #
    cC
    clt
    wbr
    #
    vk
    @0
    crab
    #
    cr
    clt
    csup
    #
    @0
    fourierdlem25.i
    wph
    @16
    @0
    @17
    @15
    vk
    @0
    ssrab2
    #
    wph
    cr
    clt
    wor
    #
    @16
    cfn
    wcel
    #
    @16
    c0
    wne
    #
    @16
    cr
    wss
    #
    @17
    @16
    wcel
    @19
    wph
    ltso
    a1i
    @20
    wph
    @0
    cfn
    wcel
    @16
    @0
    wss
    @20
    cc0
    cM
    fzofi
    @18
    @0
    @16
    ssfi
    mp2an
    a1i
    wph
    cc0
    @16
    wcel
    #
    @21
    wph
    cc0
    @0
    wcel
    #
    cc0
    cQ
    cfv
    #
    cC
    clt
    wbr
    #
    @23
    wph
    cc0
    cz
    wcel
    cM
    cz
    wcel
    #
    cc0
    cM
    clt
    wbr
    @24
    wph
    0zd
    wph
    cM
    fourierdlem25.m
    nnzd
    #
    wph
    cM
    fourierdlem25.m
    nngt0d
    cc0
    cM
    fzolb
    syl3anbrc
    #
    wph
    @25
    cC
    wph
    cc0
    cM
    cfz
    co
    #
    cr
    cc0
    cQ
    fourierdlem25.qf
    wph
    @24
    cc0
    @30
    wcel
    #
    @29
    cc0
    cc0
    cM
    elfzofz
    syl
    #
    ffvelrnd
    #
    wph
    @25
    cM
    cQ
    cfv
    #
    cicc
    co
    #
    cr
    cC
    wph
    @25
    @34
    @33
    wph
    @30
    cr
    cM
    cQ
    fourierdlem25.qf
    wph
    cM
    cc0
    cuz
    cfv
    #
    wcel
    cM
    @30
    wcel
    wph
    cM
    cn0
    @36
    wph
    cM
    fourierdlem25.m
    nnnn0d
    nn0uz
    syl6eleq
    cc0
    cM
    eluzfz2
    syl
    ffvelrnd
    #
    iccssred
    fourierdlem25.cel
    sseldd
    #
    wph
    @25
    cxr
    wcel
    #
    @34
    cxr
    wcel
    #
    cC
    @35
    wcel
    #
    @25
    cC
    cle
    wbr
    wph
    @25
    @33
    rexrd
    #
    wph
    @34
    @37
    rexrd
    #
    fourierdlem25.cel
    @25
    @34
    cC
    iccgelb
    syl3anc
    wph
    cC
    @25
    wph
    cC
    @25
    wceq
    #
    cC
    cQ
    crn
    #
    wcel
    #
    fourierdlem25.cnel
    wph
    @44
    wa
    #
    cC
    @25
    @45
    wph
    @44
    simpr
    @47
    cQ
    @30
    wfn
    #
    @31
    @25
    @45
    wcel
    wph
    @48
    @44
    wph
    @30
    cr
    cQ
    wf
    @48
    fourierdlem25.qf
    @30
    cr
    cQ
    ffn
    syl
    #
    adantr
    wph
    @31
    @44
    @32
    adantr
    @30
    cc0
    cQ
    fnfvelrn
    syl2anc
    eqeltrd
    mtand
    neqned
    leneltd
    @15
    @26
    vk
    cc0
    @0
    @13
    cc0
    wceq
    @14
    @25
    cC
    clt
    @13
    cc0
    cQ
    fveq2
    breq1d
    elrab
    sylanbrc
    @16
    cc0
    ne0i
    syl
    @22
    wph
    @16
    @0
    cr
    @18
    @0
    @30
    cr
    cc0
    cM
    fzossfz
    #
    @30
    cz
    cr
    cc0
    cM
    fzssz
    #
    zssre
    sstri
    #
    sstri
    #
    sstri
    a1i
    cr
    @16
    clt
    fisupcl
    syl13anc
    #
    sseldi
    syl5eqel
    #
    wph
    @2
    @4
    cC
    wph
    @2
    wph
    @30
    cr
    cI
    cQ
    fourierdlem25.qf
    wph
    @0
    @30
    cI
    @50
    @55
    sseldi
    ffvelrnd
    rexrd
    wph
    @4
    wph
    @30
    cr
    @3
    cQ
    fourierdlem25.qf
    wph
    @1
    @3
    @30
    wcel
    #
    @55
    cc0
    cM
    cI
    fzofzp1
    syl
    #
    ffvelrnd
    #
    rexrd
    @38
    wph
    @1
    @2
    cC
    clt
    wbr
    #
    wph
    cI
    @16
    wcel
    @1
    @59
    wa
    wph
    cI
    @17
    @16
    fourierdlem25.i
    @54
    syl5eqel
    @15
    @59
    vk
    cI
    @0
    @13
    cI
    wceq
    @14
    @2
    cC
    clt
    @13
    cI
    cQ
    fveq2
    breq1d
    elrab
    sylib
    simprd
    wph
    cC
    @4
    clt
    wbr
    @4
    cC
    cle
    wbr
    #
    wn
    wph
    @60
    @4
    cC
    clt
    wbr
    #
    @4
    cC
    wceq
    #
    wo
    #
    wph
    @61
    wn
    #
    @62
    wn
    #
    wa
    @63
    wn
    wph
    @64
    @65
    wph
    @61
    @3
    cI
    cle
    wbr
    #
    wph
    cI
    cr
    wcel
    #
    @66
    wn
    #
    wph
    @0
    cr
    cI
    @53
    @55
    sseldi
    @67
    cI
    @3
    clt
    wbr
    @68
    cI
    ltp1
    @67
    cI
    @3
    @67
    id
    cI
    peano2re
    ltnled
    mpbid
    syl
    wph
    @61
    wa
    #
    @3
    @17
    cI
    cle
    @69
    @16
    cz
    wss
    #
    vh
    cv
    #
    vm
    cv
    #
    cle
    wbr
    #
    vh
    @16
    wral
    #
    vm
    cz
    wrex
    #
    @3
    @16
    wcel
    #
    @3
    @17
    cle
    wbr
    @70
    @69
    @16
    @0
    cz
    @18
    @0
    @30
    cz
    @50
    @51
    sstri
    sstri
    a1i
    wph
    @75
    @61
    wph
    @27
    @71
    cM
    cle
    wbr
    #
    vh
    @16
    wral
    #
    @75
    @28
    wph
    @77
    vh
    @16
    @71
    @16
    wcel
    #
    @77
    wph
    @79
    @71
    @0
    wcel
    @77
    @15
    vk
    @71
    @0
    elrabi
    @71
    cM
    elfzo0le
    syl
    adantl
    ralrimiva
    @74
    @78
    vm
    cM
    cz
    @72
    cM
    wceq
    @73
    @77
    vh
    @16
    @72
    cM
    @71
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    adantr
    @69
    @3
    @0
    wcel
    #
    @61
    @76
    @69
    @3
    @36
    wcel
    #
    @27
    @3
    cM
    clt
    wbr
    @80
    wph
    @81
    @61
    wph
    @56
    @81
    @57
    @3
    cc0
    cM
    elfzuz
    syl
    adantr
    wph
    @27
    @61
    @28
    adantr
    #
    @69
    @3
    cM
    wph
    @3
    cr
    wcel
    @61
    wph
    @30
    cr
    @3
    @52
    @57
    sseldi
    adantr
    @69
    cM
    @82
    zred
    wph
    @3
    cM
    cle
    wbr
    #
    @61
    wph
    @56
    @83
    @57
    @3
    cc0
    cM
    elfzle2
    syl
    adantr
    @69
    cM
    @3
    @69
    cM
    @3
    wceq
    #
    cC
    @4
    cle
    wbr
    #
    @69
    @61
    @85
    wn
    wph
    @61
    simpr
    #
    @69
    @4
    cC
    wph
    @4
    cr
    wcel
    @61
    @58
    adantr
    wph
    cC
    cr
    wcel
    @61
    @38
    adantr
    ltnled
    mpbid
    wph
    @84
    @85
    @61
    wph
    @84
    wa
    cC
    @34
    @4
    cle
    wph
    cC
    @34
    cle
    wbr
    #
    @84
    wph
    @39
    @40
    @41
    @87
    @42
    @43
    fourierdlem25.cel
    @25
    @34
    cC
    iccleub
    syl3anc
    adantr
    @84
    @34
    @4
    wceq
    wph
    cM
    @3
    cQ
    fveq2
    adantl
    breqtrd
    adantlr
    mtand
    neqned
    leneltd
    @3
    cc0
    cM
    elfzo2
    syl3anbrc
    @86
    @15
    @61
    vk
    @3
    @0
    @13
    @3
    wceq
    @14
    @4
    cC
    clt
    @13
    @3
    cQ
    fveq2
    breq1d
    elrab
    sylanbrc
    vm
    vh
    @16
    @3
    suprzub
    syl3anc
    fourierdlem25.i
    syl6breqr
    mtand
    wph
    @62
    @46
    fourierdlem25.cnel
    wph
    @62
    wa
    #
    cC
    @4
    @45
    @62
    cC
    @4
    wceq
    #
    wph
    @62
    @89
    @4
    cC
    eqcom
    biimpi
    adantl
    @88
    @48
    @56
    @4
    @45
    wcel
    wph
    @48
    @62
    @49
    adantr
    wph
    @56
    @62
    @57
    adantr
    @30
    @3
    cQ
    fnfvelrn
    syl2anc
    eqeltrd
    mtand
    jca
    @61
    @62
    pm4.56
    sylib
    wph
    @4
    cC
    @58
    @38
    leloed
    mtbird
    wph
    cC
    @4
    @38
    @58
    ltnled
    mpbird
    eliood
    @12
    @6
    vj
    cI
    @0
    @7
    cI
    wceq
    #
    @11
    @5
    cC
    @90
    @8
    @2
    @10
    @4
    cioo
    @7
    cI
    cQ
    fveq2
    @90
    @9
    @3
    cQ
    @7
    cI
    c1
    caddc
    oveq1
    fveq2d
    oveq12d
    eleq2d
    rspcev
    syl2anc
end
