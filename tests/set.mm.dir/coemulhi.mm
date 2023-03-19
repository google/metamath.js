include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "cof.mm"
include "ccoe.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cmin.mm"
include "csu.mm"
include "csn.mm"
include "cn0.mm"
include "wceq.mm"
include "cdgr.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "nn0addcl.mm"
include "syl2an.mm"
include "coemul.mm"
include "mpd3an3.mm"
include "cle.mm"
include "wbr.mm"
include "adantl.mm"
include "nn0ge0d.mm"
include "adantr.mm"
include "nn0red.mm"
include "addge01d.mm"
include "mpbid.mm"
include "cuz.mm"
include "cz.mm"
include "wb.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "nn0zd.mm"
include "elfz5.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "snssd.mm"
include "cc.mm"
include "elsni.mm"
include "fveq2.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "syl.mm"
include "recnd.mm"
include "pncan2d.mm"
include "oveq2d.mm"
include "wf.mm"
include "coef3.mm"
include "ffvelrnd.mm"
include "mulcld.mm"
include "eqeltrd.mm"
include "cdif.mm"
include "wn.mm"
include "wne.mm"
include "wi.mm"
include "simpl.mm"
include "eldifi.mm"
include "elfznn0.mm"
include "dgrub.mm"
include "3expia.mm"
include "necon1bd.mm"
include "imp.mm"
include "oveq1d.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "fznn0sub.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "cr.mm"
include "leadd1d.mm"
include "lesubadd2d.mm"
include "bitr4d.mm"
include "notbid.mm"
include "biimpa.mm"
include "simpr.mm"
include "syldan.mm"
include "mul01d.mm"
include "wo.mm"
include "eldifsni.mm"
include "letri3d.mm"
include "necon3abid.mm"
include "ianor.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "fzfid.mm"
include "fsumss.mm"
include "sumsn.mm"
include "3eqtr2d.mm"

theorem coemulhi
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume coefv0.1: |- A = ( coeff ` F )
  assume coeadd.2: |- B = ( coeff ` G )
  assume coemulhi.3: |- M = ( deg ` F )
  assume coemulhi.4: |- N = ( deg ` G )


  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) ) -> ( ( coeff ` ( F oF x. G ) ) ` ( M + N ) ) = ( ( A ` M ) x. ( B ` N ) ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    cM
    cN
    caddc
    co
    #
    cF
    cG
    cmul
    cof
    co
    ccoe
    cfv
    cfv
    #
    cc0
    @4
    cfz
    co
    #
    vk
    cv
    #
    cA
    cfv
    #
    @4
    @7
    cmin
    co
    #
    cB
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    cM
    csn
    #
    @11
    vk
    csu
    #
    cM
    cA
    cfv
    #
    cN
    cB
    cfv
    #
    cmul
    co
    #
    @1
    @2
    @4
    cn0
    wcel
    #
    @5
    @12
    wceq
    @1
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    @18
    @2
    @1
    cM
    cF
    cdgr
    cfv
    cn0
    coemulhi.3
    cS
    cF
    dgrcl
    syl5eqel
    #
    @2
    cN
    cG
    cdgr
    cfv
    cn0
    coemulhi.4
    cS
    cG
    dgrcl
    syl5eqel
    #
    cM
    cN
    nn0addcl
    syl2an
    #
    cA
    cB
    cS
    vk
    cF
    cG
    @4
    coefv0.1
    coeadd.2
    coemul
    mpd3an3
    @3
    @13
    @6
    @11
    vk
    @3
    cM
    @6
    @3
    cM
    @6
    wcel
    #
    cM
    @4
    cle
    wbr
    #
    @3
    cc0
    cN
    cle
    wbr
    @25
    @3
    cN
    @2
    @20
    @1
    @22
    adantl
    #
    nn0ge0d
    @3
    cM
    cN
    @3
    cM
    @1
    @19
    @2
    @21
    adantr
    #
    nn0red
    #
    @3
    cN
    @26
    nn0red
    #
    addge01d
    mpbid
    @3
    cM
    cc0
    cuz
    cfv
    #
    wcel
    @4
    cz
    wcel
    @24
    @25
    wb
    @3
    cM
    cn0
    @30
    @27
    nn0uz
    syl6eleq
    @3
    @4
    @23
    nn0zd
    cM
    cc0
    @4
    elfz5
    syl2anc
    mpbird
    snssd
    @3
    @7
    @13
    wcel
    #
    wa
    #
    @11
    @15
    @4
    cM
    cmin
    co
    #
    cB
    cfv
    #
    cmul
    co
    #
    cc
    @32
    @7
    cM
    wceq
    #
    @11
    @35
    wceq
    @31
    @36
    @3
    @7
    cM
    elsni
    adantl
    @36
    @8
    @15
    @10
    @34
    cmul
    @7
    cM
    cA
    fveq2
    @36
    @9
    @33
    cB
    @7
    cM
    @4
    cmin
    oveq2
    fveq2d
    oveq12d
    #
    syl
    @3
    @35
    cc
    wcel
    #
    @31
    @3
    @35
    @17
    cc
    @3
    @34
    @16
    @15
    cmul
    @3
    @33
    cN
    cB
    @3
    cM
    cN
    @3
    cM
    @28
    recnd
    @3
    cN
    @29
    recnd
    pncan2d
    fveq2d
    oveq2d
    #
    @3
    @15
    @16
    @3
    cn0
    cc
    cM
    cA
    @1
    cn0
    cc
    cA
    wf
    #
    @2
    cA
    cS
    cF
    coefv0.1
    coef3
    adantr
    #
    @27
    ffvelrnd
    @3
    cn0
    cc
    cN
    cB
    @2
    cn0
    cc
    cB
    wf
    #
    @1
    cB
    cS
    cG
    coeadd.2
    coef3
    adantl
    #
    @26
    ffvelrnd
    mulcld
    eqeltrd
    #
    adantr
    eqeltrd
    @3
    @7
    @6
    @13
    cdif
    wcel
    #
    wa
    #
    @7
    cM
    cle
    wbr
    #
    wn
    #
    @11
    cc0
    wceq
    cM
    @7
    cle
    wbr
    #
    wn
    #
    @46
    @48
    wa
    #
    @11
    cc0
    @10
    cmul
    co
    cc0
    @51
    @8
    cc0
    @10
    cmul
    @46
    @48
    @8
    cc0
    wceq
    @46
    @47
    @8
    cc0
    @3
    @1
    @7
    cn0
    wcel
    #
    @8
    cc0
    wne
    #
    @47
    wi
    @45
    @1
    @2
    simpl
    @45
    @7
    @6
    wcel
    #
    @52
    @7
    @6
    @13
    eldifi
    #
    @7
    @4
    elfznn0
    #
    syl
    #
    @1
    @52
    @53
    @47
    cA
    cS
    cF
    @7
    cM
    coefv0.1
    coemulhi.3
    dgrub
    3expia
    syl2an
    necon1bd
    imp
    oveq1d
    @51
    @10
    @51
    cn0
    cc
    @9
    cB
    @3
    @42
    @45
    @48
    @43
    ad2antrr
    @51
    @54
    @9
    cn0
    wcel
    #
    @45
    @54
    @3
    @48
    @55
    ad2antlr
    @7
    cc0
    @4
    fznn0sub
    #
    syl
    ffvelrnd
    mul02d
    eqtrd
    @46
    @50
    wa
    #
    @11
    @8
    cc0
    cmul
    co
    cc0
    @60
    @10
    cc0
    @8
    cmul
    @46
    @50
    @9
    cN
    cle
    wbr
    #
    wn
    #
    @10
    cc0
    wceq
    #
    @46
    @50
    @62
    @46
    @49
    @61
    @46
    @49
    @4
    @7
    cN
    caddc
    co
    cle
    wbr
    @61
    @46
    cM
    @7
    cN
    @3
    cM
    cr
    wcel
    @45
    @28
    adantr
    #
    @46
    @7
    @46
    @54
    @52
    @45
    @54
    @3
    @55
    adantl
    @56
    syl
    nn0red
    #
    @3
    cN
    cr
    wcel
    @45
    @29
    adantr
    #
    leadd1d
    @46
    @4
    @7
    cN
    @46
    @4
    @3
    @18
    @45
    @23
    adantr
    nn0red
    @65
    @66
    lesubadd2d
    bitr4d
    notbid
    biimpa
    @46
    @62
    @63
    @46
    @61
    @10
    cc0
    @3
    @2
    @58
    @10
    cc0
    wne
    #
    @61
    wi
    @45
    @1
    @2
    simpr
    @45
    @54
    @58
    @55
    @59
    syl
    @2
    @58
    @67
    @61
    cB
    cS
    cG
    @9
    cN
    coeadd.2
    coemulhi.4
    dgrub
    3expia
    syl2an
    necon1bd
    imp
    syldan
    oveq2d
    @60
    @8
    @60
    cn0
    cc
    @7
    cA
    @3
    @40
    @45
    @50
    @41
    ad2antrr
    @45
    @52
    @3
    @50
    @57
    ad2antlr
    ffvelrnd
    mul01d
    eqtrd
    @46
    @47
    @49
    wa
    #
    wn
    #
    @48
    @50
    wo
    @46
    @7
    cM
    wne
    #
    @69
    @45
    @70
    @3
    @7
    @6
    cM
    eldifsni
    adantl
    @46
    @68
    @7
    cM
    @46
    @7
    cM
    @65
    @64
    letri3d
    necon3abid
    mpbid
    @47
    @49
    ianor
    sylib
    mpjaodan
    @3
    cc0
    @4
    fzfid
    fsumss
    @3
    @14
    @35
    @17
    @3
    @19
    @38
    @14
    @35
    wceq
    @27
    @44
    @11
    @35
    vk
    cM
    cn0
    @37
    sumsn
    syl2anc
    @39
    eqtrd
    3eqtr2d
end
