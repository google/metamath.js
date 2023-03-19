include "ccofu.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "cfth.mm"
include "cfunc.mm"
include "wrel.mm"
include "wcel.mm"
include "wceq.mm"
include "relfunc.mm"
include "fthfunc.mm"
include "sseldi.mm"
include "cofucl.mm"
include "1st2nd.mm"
include "sylancr.mm"
include "wbr.mm"
include "cv.mm"
include "chom.mm"
include "wf1.mm"
include "cbs.mm"
include "wral.mm"
include "1st2ndbr.mm"
include "wa.mm"
include "ccom.mm"
include "eqid.mm"
include "relfth.mm"
include "adantr.mm"
include "funcf1.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "simprr.mm"
include "fthf1.mm"
include "f1co.mm"
include "syl2anc.mm"
include "cofu2nd.mm"
include "eqidd.mm"
include "cofu1.mm"
include "oveq12d.mm"
include "f1eq123d.mm"
include "mpbird.mm"
include "ralrimivva.mm"
include "isfth2.mm"
include "sylanbrc.mm"
include "df-br.mm"
include "sylib.mm"
include "eqeltrd.mm"

theorem cofth
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  assume cofth.f: |- ( ph -> F e. ( C Faith D ) )
  assume cofth.g: |- ( ph -> G e. ( D Faith E ) )


  assert |- ( ph -> ( G o.func F ) e. ( C Faith E ) )

  proof
    wph
    cG
    cF
    ccofu
    co
    #
    @0
    c1st
    cfv
    #
    @0
    c2nd
    cfv
    #
    cop
    #
    cC
    cE
    cfth
    co
    #
    wph
    cC
    cE
    cfunc
    co
    #
    wrel
    #
    @0
    @5
    wcel
    #
    @0
    @3
    wceq
    cC
    cE
    relfunc
    #
    wph
    cC
    cD
    cE
    cF
    cG
    wph
    cC
    cD
    cfth
    co
    #
    cC
    cD
    cfunc
    co
    #
    cF
    cC
    cD
    fthfunc
    cofth.f
    sseldi
    #
    wph
    cD
    cE
    cfth
    co
    #
    cD
    cE
    cfunc
    co
    #
    cG
    cD
    cE
    fthfunc
    cofth.g
    sseldi
    #
    cofucl
    #
    @0
    @5
    1st2nd
    sylancr
    wph
    @1
    @2
    @4
    wbr
    #
    @3
    @4
    wcel
    wph
    @1
    @2
    @5
    wbr
    #
    vx
    cv
    #
    vy
    cv
    #
    cC
    chom
    cfv
    #
    co
    #
    @18
    @1
    cfv
    #
    @19
    @1
    cfv
    #
    cE
    chom
    cfv
    #
    co
    #
    @18
    @19
    @2
    co
    #
    wf1
    #
    vy
    cC
    cbs
    cfv
    #
    wral
    vx
    @28
    wral
    @16
    wph
    @6
    @7
    @17
    @8
    @15
    @0
    @5
    1st2ndbr
    sylancr
    wph
    @27
    vx
    vy
    @28
    @28
    wph
    @18
    @28
    wcel
    #
    @19
    @28
    wcel
    #
    wa
    #
    wa
    #
    @27
    @21
    @18
    cF
    c1st
    cfv
    #
    cfv
    #
    cG
    c1st
    cfv
    #
    cfv
    #
    @19
    @33
    cfv
    #
    @35
    cfv
    #
    @24
    co
    #
    @34
    @37
    cG
    c2nd
    cfv
    #
    co
    #
    @18
    @19
    cF
    c2nd
    cfv
    #
    co
    #
    ccom
    #
    wf1
    #
    @32
    @34
    @37
    cD
    chom
    cfv
    #
    co
    #
    @39
    @41
    wf1
    @21
    @47
    @43
    wf1
    @45
    @32
    cD
    cbs
    cfv
    #
    cD
    cE
    @35
    @40
    @46
    @24
    @34
    @37
    @48
    eqid
    #
    @46
    eqid
    #
    @24
    eqid
    #
    @32
    @12
    wrel
    cG
    @12
    wcel
    #
    @35
    @40
    @12
    wbr
    cD
    cE
    relfth
    wph
    @52
    @31
    cofth.g
    adantr
    cG
    @12
    1st2ndbr
    sylancr
    @32
    @28
    @48
    @18
    @33
    @32
    @28
    @48
    cC
    cD
    @33
    @42
    @28
    eqid
    #
    @49
    @32
    @10
    wrel
    cF
    @10
    wcel
    #
    @33
    @42
    @10
    wbr
    cC
    cD
    relfunc
    wph
    @54
    @31
    @11
    adantr
    #
    cF
    @10
    1st2ndbr
    sylancr
    funcf1
    #
    wph
    @29
    @30
    simprl
    #
    ffvelrnd
    @32
    @28
    @48
    @19
    @33
    @56
    wph
    @29
    @30
    simprr
    #
    ffvelrnd
    fthf1
    @32
    @28
    cC
    cD
    @33
    @42
    @20
    @46
    @18
    @19
    @53
    @20
    eqid
    #
    @50
    @32
    @9
    wrel
    cF
    @9
    wcel
    #
    @33
    @42
    @9
    wbr
    cC
    cD
    relfth
    wph
    @60
    @31
    cofth.f
    adantr
    cF
    @9
    1st2ndbr
    sylancr
    @57
    @58
    fthf1
    @21
    @47
    @39
    @41
    @43
    f1co
    syl2anc
    @32
    @21
    @21
    @25
    @39
    @26
    @44
    @32
    @28
    cC
    cD
    cE
    cF
    cG
    @18
    @19
    @53
    @55
    wph
    cG
    @13
    wcel
    @31
    @14
    adantr
    #
    @57
    @58
    cofu2nd
    @32
    @21
    eqidd
    @32
    @22
    @36
    @23
    @38
    @24
    @32
    @28
    cC
    cD
    cE
    cF
    cG
    @18
    @53
    @55
    @61
    @57
    cofu1
    @32
    @28
    cC
    cD
    cE
    cF
    cG
    @19
    @53
    @55
    @61
    @58
    cofu1
    oveq12d
    f1eq123d
    mpbird
    ralrimivva
    vx
    vy
    @28
    cC
    cE
    @1
    @2
    @20
    @24
    @53
    @59
    @51
    isfth2
    sylanbrc
    @1
    @2
    @4
    df-br
    sylib
    eqeltrd
end
