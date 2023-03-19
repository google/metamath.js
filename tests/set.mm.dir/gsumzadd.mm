include "cun.mm"
include "csupp.mm"
include "co.mm"
include "eqid.mm"
include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "submss.mm"
include "syl.mm"
include "fssd.mm"
include "crn.mm"
include "wf.mm"
include "frn.mm"
include "cntzidss.mm"
include "syl2anc.mm"
include "cof.mm"
include "cv.mm"
include "wa.mm"
include "submcl.mm"
include "3expb.mm"
include "sylan.mm"
include "inidm.mm"
include "off.mm"
include "cdif.mm"
include "cres.mm"
include "cgsu.mm"
include "csn.mm"
include "adantr.mm"
include "cvv.mm"
include "cmnd.mm"
include "vex.mm"
include "a1i.mm"
include "simpl.mm"
include "fssres.mm"
include "syl2an.mm"
include "resss.mm"
include "rnss.mm"
include "ax-mp.mm"
include "sylancl.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wfun.mm"
include "cfn.mm"
include "ffun.mm"
include "funres.mm"
include "fsuppimpd.mm"
include "fex.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ressuppss.mm"
include "ssfi.mm"
include "wb.mm"
include "resfunexg.mm"
include "isfsupp.mm"
include "mpbir2and.mm"
include "gsumzsubmcl.mm"
include "snssd.mm"
include "cntz2ss.mm"
include "sstrd.mm"
include "eldifi.mm"
include "adantl.mm"
include "ffvelrn.mm"
include "sseldd.mm"
include "gsumzaddlem.mm"

theorem gsumzadd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let c.0: class .0.
  let cZ: class Z
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cW: class W
  assume gsumzadd.b: |- B = ( Base ` G )
  assume gsumzadd.0: |- .0. = ( 0g ` G )
  assume gsumzadd.p: |- .+ = ( +g ` G )
  assume gsumzadd.z: |- Z = ( Cntz ` G )
  assume gsumzadd.g: |- ( ph -> G e. Mnd )
  assume gsumzadd.a: |- ( ph -> A e. V )
  assume gsumzadd.fn: |- ( ph -> F finSupp .0. )
  assume gsumzadd.hn: |- ( ph -> H finSupp .0. )
  assume gsumzadd.s: |- ( ph -> S e. ( SubMnd ` G ) )
  assume gsumzadd.c: |- ( ph -> S C_ ( Z ` S ) )
  assume gsumzadd.f: |- ( ph -> F : A --> S )
  assume gsumzadd.h: |- ( ph -> H : A --> S )


  assert |- ( ph -> ( G gsum ( F oF .+ H ) ) = ( ( G gsum F ) .+ ( G gsum H ) ) )

  proof
    wph
    vx
    cA
    cB
    c.pl
    vk
    cF
    cG
    cH
    cV
    cF
    cH
    cun
    c.0
    csupp
    co
    #
    c.0
    cZ
    gsumzadd.b
    gsumzadd.0
    gsumzadd.p
    gsumzadd.z
    gsumzadd.g
    gsumzadd.a
    gsumzadd.fn
    gsumzadd.hn
    @0
    eqid
    wph
    cA
    cS
    cB
    cF
    gsumzadd.f
    wph
    cS
    cG
    csubmnd
    cfv
    wcel
    #
    cS
    cB
    wss
    #
    gsumzadd.s
    cB
    cS
    cG
    gsumzadd.b
    submss
    syl
    #
    fssd
    wph
    cA
    cS
    cB
    cH
    gsumzadd.h
    @3
    fssd
    wph
    cS
    cS
    cZ
    cfv
    #
    wss
    #
    cF
    crn
    #
    cS
    wss
    #
    @6
    @6
    cZ
    cfv
    wss
    gsumzadd.c
    wph
    cA
    cS
    cF
    wf
    #
    @7
    gsumzadd.f
    cA
    cS
    cF
    frn
    syl
    cS
    @6
    cG
    cZ
    gsumzadd.z
    cntzidss
    syl2anc
    wph
    @5
    cH
    crn
    #
    cS
    wss
    #
    @9
    @9
    cZ
    cfv
    wss
    #
    gsumzadd.c
    wph
    cA
    cS
    cH
    wf
    #
    @10
    gsumzadd.h
    cA
    cS
    cH
    frn
    syl
    cS
    @9
    cG
    cZ
    gsumzadd.z
    cntzidss
    syl2anc
    #
    wph
    @5
    cF
    cH
    c.pl
    cof
    co
    #
    crn
    #
    cS
    wss
    #
    @15
    @15
    cZ
    cfv
    wss
    gsumzadd.c
    wph
    cA
    cS
    @14
    wf
    @16
    wph
    vx
    vy
    cA
    cA
    cA
    c.pl
    cS
    cS
    cS
    cF
    cH
    cV
    cV
    wph
    @1
    vx
    cv
    #
    cS
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    #
    wa
    @17
    @19
    c.pl
    co
    cS
    wcel
    #
    gsumzadd.s
    @1
    @18
    @20
    @21
    c.pl
    cS
    cG
    @17
    @19
    gsumzadd.p
    submcl
    3expb
    sylan
    gsumzadd.f
    gsumzadd.h
    gsumzadd.a
    gsumzadd.a
    cA
    inidm
    off
    cA
    cS
    @14
    frn
    syl
    cS
    @15
    cG
    cZ
    gsumzadd.z
    cntzidss
    syl2anc
    wph
    @17
    cA
    wss
    #
    vk
    cv
    #
    cA
    @17
    cdif
    wcel
    #
    wa
    #
    wa
    #
    cS
    cG
    cH
    @17
    cres
    #
    cgsu
    co
    #
    csn
    #
    cZ
    cfv
    #
    @23
    cF
    cfv
    #
    @26
    cS
    @4
    @30
    wph
    @5
    @25
    gsumzadd.c
    adantr
    @26
    @2
    @29
    cS
    wss
    @4
    @30
    wss
    wph
    @2
    @25
    @3
    adantr
    @26
    @28
    cS
    @26
    @17
    cS
    @27
    cG
    cvv
    c.0
    cZ
    gsumzadd.0
    gsumzadd.z
    wph
    cG
    cmnd
    wcel
    @25
    gsumzadd.g
    adantr
    @17
    cvv
    wcel
    #
    @26
    vx
    vex
    #
    a1i
    wph
    @1
    @25
    gsumzadd.s
    adantr
    wph
    @12
    @22
    @17
    cS
    @27
    wf
    @25
    gsumzadd.h
    @22
    @24
    simpl
    cA
    cS
    @17
    cH
    fssres
    syl2an
    @26
    @11
    @27
    crn
    #
    @9
    wss
    #
    @34
    @34
    cZ
    cfv
    wss
    wph
    @11
    @25
    @13
    adantr
    @27
    cH
    wss
    @35
    cH
    @17
    resss
    @27
    cH
    rnss
    ax-mp
    @9
    @34
    cG
    cZ
    gsumzadd.z
    cntzidss
    sylancl
    @26
    @27
    c.0
    cfsupp
    wbr
    #
    @27
    wfun
    #
    @27
    c.0
    csupp
    co
    #
    cfn
    wcel
    #
    wph
    @37
    @25
    wph
    cH
    wfun
    #
    @37
    wph
    @12
    @40
    gsumzadd.h
    cA
    cS
    cH
    ffun
    syl
    #
    @17
    cH
    funres
    syl
    adantr
    @26
    cH
    c.0
    csupp
    co
    #
    cfn
    wcel
    #
    @38
    @42
    wss
    #
    @39
    wph
    @43
    @25
    wph
    cH
    c.0
    gsumzadd.hn
    fsuppimpd
    adantr
    wph
    @44
    @25
    wph
    cH
    cvv
    wcel
    #
    c.0
    cvv
    wcel
    #
    @44
    wph
    @12
    cA
    cV
    wcel
    @45
    gsumzadd.h
    gsumzadd.a
    cA
    cS
    cV
    cH
    fex
    syl2anc
    c.0
    cG
    c0g
    cfv
    cvv
    gsumzadd.0
    cG
    c0g
    fvex
    eqeltri
    #
    @17
    cH
    cvv
    cvv
    c.0
    ressuppss
    sylancl
    adantr
    @42
    @38
    ssfi
    syl2anc
    wph
    @36
    @37
    @39
    wa
    wb
    #
    @25
    wph
    @27
    cvv
    wcel
    #
    @46
    @48
    wph
    @40
    @32
    @49
    @41
    @33
    cH
    @17
    cvv
    resfunexg
    sylancl
    @47
    @27
    cvv
    cvv
    c.0
    isfsupp
    sylancl
    adantr
    mpbir2and
    gsumzsubmcl
    snssd
    cB
    cS
    @29
    cG
    cZ
    gsumzadd.b
    gsumzadd.z
    cntz2ss
    syl2anc
    sstrd
    wph
    @8
    @23
    cA
    wcel
    #
    @31
    cS
    wcel
    @25
    gsumzadd.f
    @24
    @50
    @22
    @23
    cA
    @17
    eldifi
    adantl
    cA
    cS
    @23
    cF
    ffvelrn
    syl2an
    sseldd
    gsumzaddlem
end
