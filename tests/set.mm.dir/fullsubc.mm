include "cxp.mm"
include "cres.mm"
include "csubc.mm"
include "cfv.mm"
include "wcel.mm"
include "cssc.mm"
include "wbr.mm"
include "cv.mm"
include "ccid.mm"
include "co.mm"
include "cop.mm"
include "cco.mm"
include "wral.mm"
include "wa.mm"
include "wfn.mm"
include "cvv.mm"
include "homffn.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "sscres.mm"
include "mp2an.mm"
include "a1i.mm"
include "chom.mm"
include "eqid.mm"
include "ccat.mm"
include "adantr.mm"
include "sselda.mm"
include "catidcl.mm"
include "simpr.mm"
include "ovresd.mm"
include "homfval.mm"
include "eqtrd.mm"
include "eleqtrrd.mm"
include "ad3antrrr.mm"
include "wss.mm"
include "simprl.mm"
include "simprr.mm"
include "catcocl.mm"
include "simplr.mm"
include "ralrimivva.mm"
include "wceq.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "jca.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "fnssres.mm"
include "sylancr.mm"
include "issubc2.mm"
include "mpbir2and.mm"

theorem fullsubc
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let cH: class H
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cE: class E
  assume fullsubc.b: |- B = ( Base ` C )
  assume fullsubc.h: |- H = ( Homf ` C )
  assume fullsubc.c: |- ( ph -> C e. Cat )
  assume fullsubc.s: |- ( ph -> S C_ B )


  assert |- ( ph -> ( H |` ( S X. S ) ) e. ( Subcat ` C ) )

  proof
    wph
    cH
    cS
    cS
    cxp
    #
    cres
    #
    cC
    csubc
    cfv
    wcel
    @1
    cH
    cssc
    wbr
    #
    vx
    cv
    #
    cC
    ccid
    cfv
    #
    cfv
    #
    @3
    @3
    @1
    co
    #
    wcel
    #
    vg
    cv
    #
    vf
    cv
    #
    @3
    vy
    cv
    #
    cop
    vz
    cv
    #
    cC
    cco
    cfv
    #
    co
    co
    #
    @3
    @11
    @1
    co
    #
    wcel
    #
    vg
    @10
    @11
    @1
    co
    #
    wral
    #
    vf
    @3
    @10
    @1
    co
    #
    wral
    #
    vz
    cS
    wral
    #
    vy
    cS
    wral
    #
    wa
    #
    vx
    cS
    wral
    @2
    wph
    cH
    cB
    cB
    cxp
    #
    wfn
    #
    cB
    cvv
    wcel
    @2
    cB
    cC
    cH
    fullsubc.h
    fullsubc.b
    homffn
    #
    cB
    cC
    cbs
    cfv
    cvv
    fullsubc.b
    cC
    cbs
    fvex
    eqeltri
    cB
    cS
    cH
    cvv
    sscres
    mp2an
    a1i
    wph
    @22
    vx
    cS
    wph
    @3
    cS
    wcel
    #
    wa
    #
    @7
    @21
    @27
    @5
    @3
    @3
    cC
    chom
    cfv
    #
    co
    #
    @6
    @27
    cB
    cC
    @4
    @28
    @3
    fullsubc.b
    @28
    eqid
    #
    @4
    eqid
    #
    wph
    cC
    ccat
    wcel
    #
    @26
    fullsubc.c
    adantr
    #
    wph
    cS
    cB
    @3
    fullsubc.s
    sselda
    #
    catidcl
    @27
    @6
    @3
    @3
    cH
    co
    @29
    @27
    @3
    @3
    cH
    cS
    wph
    @26
    simpr
    #
    @35
    ovresd
    @27
    cB
    cC
    cH
    @28
    @3
    @3
    fullsubc.h
    fullsubc.b
    @30
    @34
    @34
    homfval
    eqtrd
    eleqtrrd
    @27
    @20
    vy
    cS
    @27
    @10
    cS
    wcel
    #
    wa
    #
    @19
    vz
    cS
    @37
    @11
    cS
    wcel
    #
    wa
    #
    @19
    @15
    vg
    @10
    @11
    @28
    co
    #
    wral
    #
    vf
    @3
    @10
    @28
    co
    #
    wral
    @39
    @15
    vf
    vg
    @42
    @40
    @39
    @9
    @42
    wcel
    #
    @8
    @40
    wcel
    #
    wa
    #
    wa
    #
    @13
    @3
    @11
    @28
    co
    #
    @14
    @46
    cB
    cC
    @12
    @9
    @8
    @28
    @3
    @10
    @11
    fullsubc.b
    @30
    @12
    eqid
    #
    @27
    @32
    @36
    @38
    @45
    @33
    ad3antrrr
    @27
    @3
    cB
    wcel
    #
    @36
    @38
    @45
    @34
    ad3antrrr
    #
    @39
    @10
    cB
    wcel
    #
    @45
    @37
    @51
    @38
    @27
    cS
    cB
    @10
    wph
    cS
    cB
    wss
    #
    @26
    fullsubc.s
    adantr
    #
    sselda
    #
    adantr
    #
    adantr
    @39
    @11
    cB
    wcel
    @45
    @37
    cS
    cB
    @11
    @27
    @52
    @36
    @53
    adantr
    sselda
    #
    adantr
    #
    @39
    @43
    @44
    simprl
    @39
    @43
    @44
    simprr
    catcocl
    @46
    @14
    @3
    @11
    cH
    co
    @47
    @46
    @3
    @11
    cH
    cS
    @27
    @26
    @36
    @38
    @45
    @35
    ad3antrrr
    @37
    @38
    @45
    simplr
    ovresd
    @46
    cB
    cC
    cH
    @28
    @3
    @11
    fullsubc.h
    fullsubc.b
    @30
    @50
    @57
    homfval
    eqtrd
    eleqtrrd
    ralrimivva
    @39
    @17
    @41
    vf
    @18
    @42
    @37
    @18
    @42
    wceq
    @38
    @37
    @18
    @3
    @10
    cH
    co
    @42
    @37
    @3
    @10
    cH
    cS
    wph
    @26
    @36
    simplr
    @27
    @36
    simpr
    ovresd
    @37
    cB
    cC
    cH
    @28
    @3
    @10
    fullsubc.h
    fullsubc.b
    @30
    @27
    @49
    @36
    @34
    adantr
    @54
    homfval
    eqtrd
    adantr
    @39
    @15
    vg
    @16
    @40
    @39
    @16
    @10
    @11
    cH
    co
    @40
    @39
    @10
    @11
    cH
    cS
    @27
    @36
    @38
    simplr
    @37
    @38
    simpr
    ovresd
    @39
    cB
    cC
    cH
    @28
    @10
    @11
    fullsubc.h
    fullsubc.b
    @30
    @55
    @56
    homfval
    eqtrd
    raleqdv
    raleqbidv
    mpbird
    ralrimiva
    ralrimiva
    jca
    ralrimiva
    wph
    vx
    vy
    vz
    cC
    cS
    @12
    @4
    vf
    vg
    cH
    @1
    fullsubc.h
    @31
    @48
    fullsubc.c
    wph
    @24
    @0
    @23
    wss
    #
    @1
    @0
    wfn
    @25
    wph
    @52
    @52
    @58
    fullsubc.s
    fullsubc.s
    cS
    cB
    cS
    cB
    xpss12
    syl2anc
    @23
    @0
    cH
    fnssres
    sylancr
    issubc2
    mpbir2and
end
