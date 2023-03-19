include "cr.mm"
include "cdv.mm"
include "co.mm"
include "cioo.mm"
include "ccncf.mm"
include "wcel.mm"
include "wf.mm"
include "cdm.mm"
include "wss.mm"
include "cv.mm"
include "caddc.mm"
include "cfv.mm"
include "cmin.mm"
include "cdiv.mm"
include "wa.mm"
include "adantr.mm"
include "elioore.mm"
include "adantl.mm"
include "readdcld.mm"
include "ffvelrnd.mm"
include "resubcld.mm"
include "cc0.mm"
include "wceq.mm"
include "eqcom.mm"
include "biimpi.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "adantll.mm"
include "wn.mm"
include "ad2antrr.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "redivcld.mm"
include "fmptd.mm"
include "ioossre.mm"
include "a1i.mm"
include "dvfre.mm"
include "syl2anc.mm"
include "cc.mm"
include "cmpt.mm"
include "cof.mm"
include "cvv.mm"
include "ovex.mm"
include "eqidd.mm"
include "offval2.mm"
include "syl6reqr.mm"
include "oveq2d.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "recnd.mm"
include "eqid.mm"
include "csn.mm"
include "cdif.mm"
include "wne.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "eqcomd.mm"
include "cres.mm"
include "cncff.mm"
include "syl.mm"
include "fourierdlem28.mm"
include "ioosscn.mm"
include "ax-resscn.mm"
include "fssd.mm"
include "wb.mm"
include "ssid.mm"
include "cncffvrn.mm"
include "mpbird.mm"
include "cxr.mm"
include "rexrd.mm"
include "clt.mm"
include "wbr.mm"
include "simpr.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "ltadd2dd.mm"
include "iooltub.mm"
include "eliood.mm"
include "fourierdlem23.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "crn.mm"
include "ctg.mm"
include "iooretop.mm"
include "tgioo2.mm"
include "eleqtri.mm"
include "dvmptconst.mm"
include "0cnd.mm"
include "constcncfg.mm"
include "dvsubcncf.mm"
include "c1.mm"
include "dvmptidg.mm"
include "1cnd.mm"
include "dvdivcncf.mm"
include "fdm.mm"
include "3syl.mm"
include "feq2d.mm"
include "mpbid.mm"

theorem fourierdlem59
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cH: class H
  let cX: class X
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem59.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem59.x: |- ( ph -> X e. RR )
  assume fourierdlem59.a: |- ( ph -> A e. RR )
  assume fourierdlem59.b: |- ( ph -> B e. RR )
  assume fourierdlem59.n0: |- ( ph -> -. 0 e. ( A (,) B ) )
  assume fourierdlem59.fdv: |- ( ph -> ( RR _D ( F |` ( ( X + A ) (,) ( X + B ) ) ) ) e. ( ( ( X + A ) (,) ( X + B ) ) -cn-> RR ) )
  assume fourierdlem59.c: |- ( ph -> C e. RR )
  assume fourierdlem59.h: |- H = ( s e. ( A (,) B ) |-> ( ( ( F ` ( X + s ) ) - C ) / s ) )

  disjoint A s
  disjoint B s
  disjoint C s
  disjoint F s
  disjoint X s
  disjoint ph s
  disjoint k x
  assert |- ( ph -> ( RR _D H ) e. ( ( A (,) B ) -cn-> RR ) )

  proof
    wph
    cr
    cH
    cdv
    co
    #
    cA
    cB
    cioo
    co
    #
    cr
    ccncf
    co
    wcel
    #
    @1
    cr
    @0
    wf
    #
    wph
    @0
    cdm
    #
    cr
    @0
    wf
    #
    @3
    wph
    @1
    cr
    cH
    wf
    @1
    cr
    wss
    #
    @5
    wph
    vs
    @1
    cX
    vs
    cv
    #
    caddc
    co
    #
    cF
    cfv
    #
    cC
    cmin
    co
    #
    @7
    cdiv
    co
    #
    cr
    cH
    wph
    @7
    @1
    wcel
    #
    wa
    #
    @10
    @7
    @13
    @9
    cC
    @13
    cr
    cr
    @8
    cF
    wph
    cr
    cr
    cF
    wf
    @12
    fourierdlem59.f
    adantr
    @13
    cX
    @7
    wph
    cX
    cr
    wcel
    @12
    fourierdlem59.x
    adantr
    #
    @12
    @7
    cr
    wcel
    wph
    @7
    cA
    cB
    elioore
    adantl
    #
    readdcld
    #
    ffvelrnd
    #
    wph
    cC
    cr
    wcel
    @12
    fourierdlem59.c
    adantr
    #
    resubcld
    #
    @15
    @13
    @7
    cc0
    @13
    @7
    cc0
    wceq
    #
    cc0
    @1
    wcel
    #
    @12
    @20
    @21
    wph
    @12
    @20
    wa
    cc0
    @7
    @1
    @20
    cc0
    @7
    wceq
    #
    @12
    @20
    @22
    @7
    cc0
    eqcom
    biimpi
    adantl
    @12
    @20
    simpl
    eqeltrd
    adantll
    wph
    @21
    wn
    @12
    @20
    fourierdlem59.n0
    ad2antrr
    pm2.65da
    neqned
    #
    redivcld
    fourierdlem59.h
    fmptd
    @6
    wph
    cA
    cB
    ioossre
    a1i
    @1
    cH
    dvfre
    syl2anc
    wph
    @4
    @1
    cr
    @0
    wph
    @0
    @1
    cc
    ccncf
    co
    #
    wcel
    #
    @1
    cc
    @0
    wf
    @4
    @1
    wceq
    wph
    @0
    cr
    vs
    @1
    @10
    cmpt
    #
    vs
    @1
    @7
    cmpt
    #
    cdiv
    cof
    co
    #
    cdv
    co
    @24
    wph
    cH
    @28
    cr
    cdv
    wph
    @28
    vs
    @1
    @11
    cmpt
    cH
    wph
    vs
    @1
    @10
    @7
    cdiv
    @26
    @27
    cvv
    cr
    cr
    @1
    cvv
    wcel
    wph
    cA
    cB
    cioo
    ovex
    a1i
    #
    @19
    @15
    wph
    @26
    eqidd
    wph
    @27
    eqidd
    offval2
    fourierdlem59.h
    syl6reqr
    oveq2d
    wph
    cr
    @26
    @27
    @1
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    #
    wph
    vs
    @1
    @10
    cc
    @26
    @13
    @10
    @19
    recnd
    @26
    eqid
    fmptd
    wph
    vs
    @1
    @7
    cc
    cc0
    csn
    cdif
    #
    @27
    @13
    @7
    cc
    wcel
    @7
    cc0
    wne
    @7
    @31
    wcel
    @13
    @7
    @15
    recnd
    @23
    @7
    cc
    cc0
    eldifsn
    sylanbrc
    @27
    eqid
    fmptd
    wph
    cr
    @26
    cdv
    co
    cr
    vs
    @1
    @9
    cmpt
    #
    vs
    @1
    cC
    cmpt
    #
    cmin
    cof
    co
    #
    cdv
    co
    @24
    wph
    @26
    @34
    cr
    cdv
    wph
    @34
    @26
    wph
    vs
    @1
    @9
    cC
    cmin
    @32
    @33
    cvv
    cr
    cr
    @29
    @17
    @18
    wph
    @32
    eqidd
    wph
    @33
    eqidd
    offval2
    eqcomd
    oveq2d
    wph
    cr
    @32
    @33
    @1
    @30
    wph
    vs
    @1
    @9
    cc
    @32
    @13
    @9
    @17
    recnd
    @32
    eqid
    fmptd
    wph
    vs
    @1
    cC
    cc
    @33
    @13
    cC
    @18
    recnd
    @33
    eqid
    fmptd
    wph
    cr
    @32
    cdv
    co
    vs
    @1
    @8
    cr
    cF
    cX
    cA
    caddc
    co
    #
    cX
    cB
    caddc
    co
    #
    cioo
    co
    #
    cres
    cdv
    co
    #
    cfv
    cmpt
    @24
    wph
    cA
    cB
    @38
    cF
    cX
    vs
    fourierdlem59.f
    fourierdlem59.x
    fourierdlem59.a
    fourierdlem59.b
    @38
    eqid
    wph
    @38
    @37
    cr
    ccncf
    co
    wcel
    #
    @37
    cr
    @38
    wf
    fourierdlem59.fdv
    @37
    cr
    @38
    cncff
    syl
    #
    fourierdlem28
    wph
    @37
    @1
    @38
    cX
    vs
    @37
    cc
    wss
    wph
    @35
    @36
    ioosscn
    a1i
    wph
    @38
    @37
    cc
    ccncf
    co
    wcel
    #
    @37
    cc
    @38
    wf
    #
    wph
    @37
    cr
    cc
    @38
    @40
    cr
    cc
    wss
    #
    wph
    ax-resscn
    a1i
    #
    fssd
    wph
    cc
    cc
    wss
    #
    @39
    @41
    @42
    wb
    @45
    wph
    cc
    ssid
    a1i
    #
    fourierdlem59.fdv
    @37
    cr
    cc
    @38
    cncffvrn
    syl2anc
    mpbird
    @1
    cc
    wss
    wph
    cA
    cB
    ioosscn
    a1i
    #
    wph
    cX
    fourierdlem59.x
    recnd
    @13
    @35
    @36
    @8
    wph
    @35
    cxr
    wcel
    @12
    wph
    @35
    wph
    cX
    cA
    fourierdlem59.x
    fourierdlem59.a
    readdcld
    rexrd
    adantr
    wph
    @36
    cxr
    wcel
    @12
    wph
    @36
    wph
    cX
    cB
    fourierdlem59.x
    fourierdlem59.b
    readdcld
    rexrd
    adantr
    @16
    @13
    cA
    @7
    cX
    wph
    cA
    cr
    wcel
    @12
    fourierdlem59.a
    adantr
    #
    @15
    @14
    @13
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @12
    cA
    @7
    clt
    wbr
    @13
    cA
    @48
    rexrd
    #
    wph
    @50
    @12
    wph
    cB
    fourierdlem59.b
    rexrd
    adantr
    #
    wph
    @12
    simpr
    #
    cA
    cB
    @7
    ioogtlb
    syl3anc
    ltadd2dd
    @13
    @7
    cB
    cX
    @15
    wph
    cB
    cr
    wcel
    @12
    fourierdlem59.b
    adantr
    @14
    @13
    @49
    @50
    @12
    @7
    cB
    clt
    wbr
    @51
    @52
    @53
    cA
    cB
    @7
    iooltub
    syl3anc
    ltadd2dd
    eliood
    fourierdlem23
    eqeltrd
    wph
    cr
    @33
    cdv
    co
    vs
    @1
    cc0
    cmpt
    @24
    wph
    vs
    @1
    cC
    cr
    @30
    @1
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    #
    wcel
    wph
    @1
    cioo
    crn
    ctg
    cfv
    @55
    cA
    cB
    iooretop
    @54
    @54
    eqid
    tgioo2
    eleqtri
    a1i
    #
    wph
    cC
    fourierdlem59.c
    recnd
    dvmptconst
    wph
    vs
    @1
    cc0
    cc
    @47
    wph
    0cnd
    @46
    constcncfg
    eqeltrd
    dvsubcncf
    eqeltrd
    wph
    cr
    @27
    cdv
    co
    vs
    @1
    c1
    cmpt
    @24
    wph
    vs
    @1
    cr
    @30
    @56
    dvmptidg
    wph
    vs
    @1
    c1
    cc
    @47
    wph
    1cnd
    @46
    constcncfg
    eqeltrd
    dvdivcncf
    eqeltrd
    #
    @1
    cc
    @0
    cncff
    @1
    cc
    @0
    fdm
    3syl
    feq2d
    mpbid
    wph
    @43
    @25
    @2
    @3
    wb
    @44
    @57
    @1
    cc
    cr
    @0
    cncffvrn
    syl2anc
    mpbird
end
