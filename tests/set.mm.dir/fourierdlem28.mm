include "cr.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "caddc.mm"
include "cfv.mm"
include "cmpt.mm"
include "cdv.mm"
include "c1.mm"
include "cmul.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "reelprrecn.mm"
include "a1i.mm"
include "wa.mm"
include "cxr.mm"
include "readdcld.mm"
include "rexrd.mm"
include "adantr.mm"
include "elioore.mm"
include "adantl.mm"
include "clt.mm"
include "wbr.mm"
include "simpr.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "ltadd2dd.mm"
include "iooltub.mm"
include "eliood.mm"
include "1red.mm"
include "wf.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "ffvelrnda.mm"
include "cc0.mm"
include "0red.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "crn.mm"
include "ctg.mm"
include "iooretop.mm"
include "eqid.mm"
include "tgioo2.mm"
include "eleqtri.mm"
include "dvmptconst.mm"
include "dvmptidg.mm"
include "dvmptadd.mm"
include "wceq.mm"
include "0p1e1.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "cres.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "wss.mm"
include "ioossre.mm"
include "resmptd.mm"
include "eqtr2d.mm"
include "oveq2d.mm"
include "eqcomi.mm"
include "3eqtrd.mm"
include "fveq2.mm"
include "dvmptco.mm"
include "mulid1d.mm"

theorem fourierdlem28
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cF: class F
  let cX: class X
  let vs: setvar s
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem28.1: |- ( ph -> F : RR --> RR )
  assume fourierdlem28.x: |- ( ph -> X e. RR )
  assume fourierdlem28.a: |- ( ph -> A e. RR )
  assume fourierdlem28.3b: |- ( ph -> B e. RR )
  assume fourierdlem28.d: |- D = ( RR _D ( F |` ( ( X + A ) (,) ( X + B ) ) ) )
  assume fourierdlem28.df: |- ( ph -> D : ( ( X + A ) (,) ( X + B ) ) --> RR )

  disjoint A s
  disjoint B s
  disjoint D s
  disjoint F s
  disjoint X s
  disjoint ph s
  disjoint A y
  disjoint s y
  disjoint B y
  disjoint D y
  disjoint F y
  disjoint X y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( RR _D ( s e. ( A (,) B ) |-> ( F ` ( X + s ) ) ) ) = ( s e. ( A (,) B ) |-> ( D ` ( X + s ) ) ) )

  proof
    wph
    cr
    vs
    cA
    cB
    cioo
    co
    #
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
    cmpt
    cdv
    co
    vs
    @0
    @2
    cD
    cfv
    #
    c1
    cmul
    co
    #
    cmpt
    vs
    @0
    @4
    cmpt
    wph
    vs
    vy
    @2
    c1
    vy
    cv
    #
    cF
    cfv
    #
    @6
    cD
    cfv
    #
    cr
    cr
    @3
    @4
    cr
    cr
    @0
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
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    #
    @12
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @9
    @10
    @2
    wph
    @9
    cxr
    wcel
    @13
    wph
    @9
    wph
    cX
    cA
    fourierdlem28.x
    fourierdlem28.a
    readdcld
    rexrd
    adantr
    wph
    @10
    cxr
    wcel
    @13
    wph
    @10
    wph
    cX
    cB
    fourierdlem28.x
    fourierdlem28.3b
    readdcld
    rexrd
    adantr
    @14
    cX
    @1
    wph
    cX
    cr
    wcel
    @13
    fourierdlem28.x
    adantr
    #
    @13
    @1
    cr
    wcel
    wph
    @1
    cA
    cB
    elioore
    adantl
    #
    readdcld
    @14
    cA
    @1
    cX
    wph
    cA
    cr
    wcel
    @13
    fourierdlem28.a
    adantr
    #
    @16
    @15
    @14
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @13
    cA
    @1
    clt
    wbr
    @14
    cA
    @17
    rexrd
    #
    wph
    @19
    @13
    wph
    cB
    fourierdlem28.3b
    rexrd
    adantr
    #
    wph
    @13
    simpr
    #
    cA
    cB
    @1
    ioogtlb
    syl3anc
    ltadd2dd
    @14
    @1
    cB
    cX
    @16
    wph
    cB
    cr
    wcel
    @13
    fourierdlem28.3b
    adantr
    @15
    @14
    @18
    @19
    @13
    @1
    cB
    clt
    wbr
    @20
    @21
    @22
    cA
    cB
    @1
    iooltub
    syl3anc
    ltadd2dd
    eliood
    #
    @14
    1red
    #
    wph
    @6
    @11
    wcel
    #
    wa
    #
    @7
    @26
    cr
    cr
    @6
    cF
    wph
    cr
    cr
    cF
    wf
    @25
    fourierdlem28.1
    adantr
    @25
    @6
    cr
    wcel
    wph
    @6
    @9
    @10
    elioore
    adantl
    ffvelrnd
    recnd
    wph
    @11
    cr
    @6
    cD
    fourierdlem28.df
    ffvelrnda
    wph
    cr
    vs
    @0
    @2
    cmpt
    cdv
    co
    vs
    @0
    cc0
    c1
    caddc
    co
    #
    cmpt
    vs
    @0
    c1
    cmpt
    wph
    vs
    cX
    cc0
    @1
    c1
    cr
    cr
    cr
    @0
    @12
    @14
    cX
    @15
    recnd
    @14
    0red
    wph
    vs
    @0
    cX
    cr
    @12
    @0
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
    @0
    cioo
    crn
    ctg
    cfv
    @29
    cA
    cB
    iooretop
    @28
    @28
    eqid
    tgioo2
    eleqtri
    a1i
    #
    wph
    cX
    fourierdlem28.x
    recnd
    dvmptconst
    @14
    @1
    @16
    recnd
    @24
    wph
    vs
    @0
    cr
    @12
    @30
    dvmptidg
    dvmptadd
    wph
    vs
    @0
    @27
    c1
    @27
    c1
    wceq
    @14
    0p1e1
    a1i
    mpteq2dva
    eqtrd
    wph
    cr
    vy
    @11
    @7
    cmpt
    #
    cdv
    co
    cr
    cF
    @11
    cres
    #
    cdv
    co
    #
    cD
    vy
    @11
    @8
    cmpt
    wph
    @31
    @32
    cr
    cdv
    wph
    @32
    vy
    cr
    @7
    cmpt
    #
    @11
    cres
    @31
    wph
    cF
    @34
    @11
    wph
    vy
    cr
    cr
    cF
    fourierdlem28.1
    feqmptd
    reseq1d
    wph
    vy
    cr
    @11
    @7
    @11
    cr
    wss
    wph
    @9
    @10
    ioossre
    a1i
    resmptd
    eqtr2d
    oveq2d
    @33
    cD
    wceq
    wph
    cD
    @33
    fourierdlem28.d
    eqcomi
    a1i
    wph
    vy
    @11
    cr
    cD
    fourierdlem28.df
    feqmptd
    3eqtrd
    @6
    @2
    cF
    fveq2
    @6
    @2
    cD
    fveq2
    dvmptco
    wph
    vs
    @0
    @5
    @4
    @14
    @4
    @14
    @4
    @14
    @11
    cr
    @2
    cD
    wph
    @11
    cr
    cD
    wf
    @13
    fourierdlem28.df
    adantr
    @23
    ffvelrnd
    recnd
    mulid1d
    mpteq2dva
    eqtrd
end
