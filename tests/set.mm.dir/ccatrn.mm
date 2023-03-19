include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cconcat.mm"
include "co.mm"
include "crn.mm"
include "cun.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "cfzo.mm"
include "wf.mm"
include "wss.mm"
include "wfn.mm"
include "cv.mm"
include "wral.mm"
include "ccatvalfn.mm"
include "wo.mm"
include "cfz.mm"
include "wceq.mm"
include "cuz.mm"
include "cn0.mm"
include "lencl.mm"
include "adantr.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "cz.mm"
include "nn0zd.mm"
include "uzid.mm"
include "syl.mm"
include "adantl.mm"
include "uzaddcl.mm"
include "syl2anc.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "fzosplit.mm"
include "eleq2d.mm"
include "elun.mm"
include "syl6bb.mm"
include "ccatval1.mm"
include "3expa.mm"
include "ssun1.mm"
include "simpl.mm"
include "wrdf.mm"
include "ffn.mm"
include "3syl.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "sseldi.mm"
include "eqeltrd.mm"
include "cmin.mm"
include "ccatval2.mm"
include "ssun2.mm"
include "simpr.mm"
include "clt.mm"
include "wbr.mm"
include "elfzouz.mm"
include "uznn0sub.mm"
include "elfzolt2.mm"
include "elfzoelz.mm"
include "zred.mm"
include "ltsubadd2d.mm"
include "mpbird.mm"
include "elfzo2.mm"
include "syl3anbrc.mm"
include "jaodan.mm"
include "ex.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "ffnfv.mm"
include "frn.mm"
include "fzoss2.mm"
include "sselda.mm"
include "eqeltrrd.mm"
include "ralrimiva.mm"
include "ccatval3.mm"
include "syl6eleqr.mm"
include "nn0addcld.mm"
include "nn0cnd.mm"
include "addcomd.mm"
include "nn0red.mm"
include "ltadd2dd.mm"
include "eqbrtrd.mm"
include "unssd.mm"
include "eqssd.mm"

theorem ccatrn
  let cB: class B
  let cS: class S
  let cT: class T
  let vx: setvar x
  let cU: class U


  assert |- ( ( S e. Word B /\ T e. Word B ) -> ran ( S ++ T ) = ( ran S u. ran T ) )

  proof
    cS
    cB
    cword
    #
    wcel
    #
    cT
    @0
    wcel
    #
    wa
    #
    cS
    cT
    cconcat
    co
    #
    crn
    #
    cS
    crn
    #
    cT
    crn
    #
    cun
    #
    @3
    cc0
    cS
    chash
    cfv
    #
    cT
    chash
    cfv
    #
    caddc
    co
    #
    cfzo
    co
    #
    @8
    @4
    wf
    #
    @5
    @8
    wss
    @3
    @4
    @12
    wfn
    #
    vx
    cv
    #
    @4
    cfv
    #
    @8
    wcel
    #
    vx
    @12
    wral
    @13
    cS
    cT
    cB
    ccatvalfn
    #
    @3
    @17
    vx
    @12
    @3
    @15
    @12
    wcel
    #
    @15
    cc0
    @9
    cfzo
    co
    #
    wcel
    #
    @15
    @9
    @11
    cfzo
    co
    #
    wcel
    #
    wo
    #
    @17
    @3
    @19
    @15
    @20
    @22
    cun
    #
    wcel
    @24
    @3
    @12
    @25
    @15
    @3
    @9
    cc0
    @11
    cfz
    co
    wcel
    #
    @12
    @25
    wceq
    @3
    @9
    cc0
    cuz
    cfv
    #
    wcel
    @11
    @9
    cuz
    cfv
    #
    wcel
    #
    @26
    @3
    @9
    cn0
    @27
    @1
    @9
    cn0
    wcel
    #
    @2
    cB
    cS
    lencl
    adantr
    #
    nn0uz
    syl6eleq
    @3
    @9
    @28
    wcel
    #
    @10
    cn0
    wcel
    #
    @29
    @3
    @9
    cz
    wcel
    #
    @32
    @3
    @9
    @31
    nn0zd
    #
    @9
    uzid
    syl
    @2
    @33
    @1
    cB
    cT
    lencl
    adantl
    #
    @10
    @9
    @9
    uzaddcl
    syl2anc
    #
    @9
    cc0
    @11
    elfzuzb
    sylanbrc
    cc0
    @11
    @9
    fzosplit
    syl
    eleq2d
    @15
    @20
    @22
    elun
    syl6bb
    @3
    @24
    @17
    @3
    @21
    @17
    @23
    @3
    @21
    wa
    #
    @16
    @15
    cS
    cfv
    #
    @8
    @1
    @2
    @21
    @16
    @39
    wceq
    cB
    cS
    cT
    @15
    ccatval1
    3expa
    #
    @38
    @6
    @8
    @39
    @6
    @7
    ssun1
    @3
    cS
    @20
    wfn
    #
    @21
    @39
    @6
    wcel
    @3
    @1
    @20
    cB
    cS
    wf
    @41
    @1
    @2
    simpl
    cB
    cS
    wrdf
    @20
    cB
    cS
    ffn
    3syl
    #
    @20
    @15
    cS
    fnfvelrn
    sylan
    sseldi
    eqeltrd
    @3
    @23
    wa
    #
    @16
    @15
    @9
    cmin
    co
    #
    cT
    cfv
    #
    @8
    @1
    @2
    @23
    @16
    @45
    wceq
    cB
    cS
    cT
    @15
    ccatval2
    3expa
    @43
    @7
    @8
    @45
    @7
    @6
    ssun2
    @43
    cT
    cc0
    @10
    cfzo
    co
    #
    wfn
    #
    @44
    @46
    wcel
    #
    @45
    @7
    wcel
    @3
    @47
    @23
    @3
    @2
    @46
    cB
    cT
    wf
    @47
    @1
    @2
    simpr
    cB
    cT
    wrdf
    @46
    cB
    cT
    ffn
    3syl
    #
    adantr
    @43
    @44
    @27
    wcel
    @10
    cz
    wcel
    #
    @44
    @10
    clt
    wbr
    #
    @48
    @43
    @44
    cn0
    @27
    @43
    @15
    @28
    wcel
    #
    @44
    cn0
    wcel
    @23
    @52
    @3
    @15
    @9
    @11
    elfzouz
    adantl
    @9
    @15
    uznn0sub
    syl
    nn0uz
    syl6eleq
    @3
    @50
    @23
    @3
    @10
    @36
    nn0zd
    adantr
    #
    @43
    @51
    @15
    @11
    clt
    wbr
    #
    @23
    @54
    @3
    @15
    @9
    @11
    elfzolt2
    adantl
    @43
    @15
    @9
    @10
    @43
    @15
    @23
    @15
    cz
    wcel
    @3
    @15
    @9
    @11
    elfzoelz
    adantl
    zred
    @43
    @9
    @3
    @34
    @23
    @35
    adantr
    zred
    @43
    @10
    @53
    zred
    ltsubadd2d
    mpbird
    @44
    cc0
    @10
    elfzo2
    syl3anbrc
    @46
    @44
    cT
    fnfvelrn
    syl2anc
    sseldi
    eqeltrd
    jaodan
    ex
    sylbid
    ralrimiv
    vx
    @12
    @8
    @4
    ffnfv
    sylanbrc
    @12
    @8
    @4
    frn
    syl
    @3
    @6
    @7
    @5
    @3
    @20
    @5
    cS
    wf
    #
    @6
    @5
    wss
    @3
    @41
    @39
    @5
    wcel
    #
    vx
    @20
    wral
    @55
    @42
    @3
    @56
    vx
    @20
    @38
    @16
    @39
    @5
    @40
    @38
    @14
    @19
    @16
    @5
    wcel
    @3
    @14
    @21
    @18
    adantr
    @3
    @20
    @12
    @15
    @3
    @29
    @20
    @12
    wss
    @37
    @9
    cc0
    @11
    fzoss2
    syl
    sselda
    @12
    @15
    @4
    fnfvelrn
    syl2anc
    eqeltrrd
    ralrimiva
    vx
    @20
    @5
    cS
    ffnfv
    sylanbrc
    @20
    @5
    cS
    frn
    syl
    @3
    @46
    @5
    cT
    wf
    #
    @7
    @5
    wss
    @3
    @47
    @15
    cT
    cfv
    #
    @5
    wcel
    #
    vx
    @46
    wral
    @57
    @49
    @3
    @59
    vx
    @46
    @3
    @15
    @46
    wcel
    #
    wa
    #
    @15
    @9
    caddc
    co
    #
    @4
    cfv
    #
    @58
    @5
    @1
    @2
    @60
    @63
    @58
    wceq
    cB
    cS
    cT
    @15
    ccatval3
    3expa
    @61
    @14
    @62
    @12
    wcel
    #
    @63
    @5
    wcel
    @3
    @14
    @60
    @18
    adantr
    @61
    @62
    @27
    wcel
    @11
    cz
    wcel
    #
    @62
    @11
    clt
    wbr
    @64
    @61
    @62
    cn0
    @27
    @61
    @15
    @9
    @61
    @15
    @27
    cn0
    @60
    @15
    @27
    wcel
    @3
    @15
    cc0
    @10
    elfzouz
    adantl
    nn0uz
    syl6eleqr
    #
    @3
    @30
    @60
    @31
    adantr
    #
    nn0addcld
    nn0uz
    syl6eleq
    @3
    @65
    @60
    @3
    @11
    @3
    @9
    @10
    @31
    @36
    nn0addcld
    nn0zd
    adantr
    @61
    @62
    @9
    @15
    caddc
    co
    @11
    clt
    @61
    @15
    @9
    @61
    @15
    @66
    nn0cnd
    @61
    @9
    @67
    nn0cnd
    addcomd
    @61
    @15
    @10
    @9
    @61
    @15
    @66
    nn0red
    @61
    @10
    @3
    @33
    @60
    @36
    adantr
    nn0red
    @61
    @9
    @67
    nn0red
    @60
    @15
    @10
    clt
    wbr
    @3
    @15
    cc0
    @10
    elfzolt2
    adantl
    ltadd2dd
    eqbrtrd
    @62
    cc0
    @11
    elfzo2
    syl3anbrc
    @12
    @62
    @4
    fnfvelrn
    syl2anc
    eqeltrrd
    ralrimiva
    vx
    @46
    @5
    cT
    ffnfv
    sylanbrc
    @46
    @5
    cT
    frn
    syl
    unssd
    eqssd
end
