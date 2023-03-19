include "csupp.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cgsu.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cn.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wa.mm"
include "cmpt.mm"
include "cvv.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wss.mm"
include "ssid.mm"
include "gsumcllem.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "gsumz.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqtrd.mm"
include "mndidcl.mm"
include "syl.mm"
include "eqeltrd.mm"
include "ex.mm"
include "cplusg.mm"
include "ccom.mm"
include "cseq.mm"
include "eqid.mm"
include "wf.mm"
include "crn.mm"
include "simprl.mm"
include "wf1.mm"
include "f1of1.mm"
include "ad2antll.mm"
include "cdm.mm"
include "suppssdm.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "f1ss.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "syl5sseqr.mm"
include "gsumval3.mm"
include "cuz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "f1f.mm"
include "fco.mm"
include "ffvelrnda.mm"
include "mndcl.mm"
include "3expb.mm"
include "sylan.mm"
include "seqcl.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfn.mm"
include "wo.mm"
include "fz1f1o.mm"
include "mpjaod.mm"

theorem gsumzcl2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let c.0: class .0.
  let cZ: class Z
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x
  let cH: class H
  let cC: class C
  let cW: class W
  assume gsumzcl.b: |- B = ( Base ` G )
  assume gsumzcl.0: |- .0. = ( 0g ` G )
  assume gsumzcl.z: |- Z = ( Cntz ` G )
  assume gsumzcl.g: |- ( ph -> G e. Mnd )
  assume gsumzcl.a: |- ( ph -> A e. V )
  assume gsumzcl.f: |- ( ph -> F : A --> B )
  assume gsumzcl.c: |- ( ph -> ran F C_ ( Z ` ran F ) )
  assume gsumzcl2.w: |- ( ph -> ( F supp .0. ) e. Fin )


  assert |- ( ph -> ( G gsum F ) e. B )

  proof
    wph
    cF
    c.0
    csupp
    co
    #
    c0
    wceq
    #
    cG
    cF
    cgsu
    co
    #
    cB
    wcel
    #
    @0
    chash
    cfv
    #
    cn
    wcel
    #
    c1
    @4
    cfz
    co
    #
    @0
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    wa
    #
    wph
    @1
    @3
    wph
    @1
    wa
    #
    @2
    c.0
    cB
    @11
    @2
    cG
    vk
    cA
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    @11
    cF
    @12
    cG
    cgsu
    wph
    cA
    cB
    cvv
    vk
    cF
    cV
    @0
    c.0
    gsumzcl.f
    gsumzcl.a
    c.0
    cvv
    wcel
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    gsumzcl.0
    cG
    c0g
    fvex
    eqeltri
    a1i
    @0
    @0
    wss
    wph
    @0
    ssid
    #
    a1i
    gsumcllem
    oveq2d
    wph
    @13
    c.0
    wceq
    #
    @1
    wph
    cG
    cmnd
    wcel
    #
    cA
    cV
    wcel
    #
    @15
    gsumzcl.g
    gsumzcl.a
    cA
    vk
    cG
    cV
    c.0
    gsumzcl.0
    gsumz
    syl2anc
    adantr
    eqtrd
    wph
    c.0
    cB
    wcel
    #
    @1
    wph
    @16
    @18
    gsumzcl.g
    cB
    cG
    c.0
    gsumzcl.b
    gsumzcl.0
    mndidcl
    syl
    adantr
    eqeltrd
    ex
    wph
    @5
    @9
    @3
    wph
    @5
    wa
    @8
    @3
    vf
    wph
    @5
    @8
    @3
    wph
    @5
    @8
    wa
    #
    wa
    #
    @2
    @4
    cG
    cplusg
    cfv
    #
    cF
    @7
    ccom
    #
    c1
    cseq
    cfv
    cB
    @20
    cA
    cB
    @21
    cF
    cG
    @7
    @4
    cV
    @22
    c.0
    csupp
    co
    #
    c.0
    cZ
    gsumzcl.b
    gsumzcl.0
    @21
    eqid
    #
    gsumzcl.z
    wph
    @16
    @19
    gsumzcl.g
    adantr
    #
    wph
    @17
    @19
    gsumzcl.a
    adantr
    wph
    cA
    cB
    cF
    wf
    #
    @19
    gsumzcl.f
    adantr
    #
    wph
    cF
    crn
    #
    @28
    cZ
    cfv
    wss
    @19
    gsumzcl.c
    adantr
    wph
    @5
    @8
    simprl
    #
    @20
    @6
    @0
    @7
    wf1
    #
    @0
    cA
    wss
    #
    @6
    cA
    @7
    wf1
    #
    @8
    @30
    wph
    @5
    @6
    @0
    @7
    f1of1
    ad2antll
    wph
    @31
    @19
    wph
    cF
    cdm
    #
    @0
    cA
    cF
    c.0
    suppssdm
    wph
    @26
    @33
    cA
    wceq
    gsumzcl.f
    cA
    cB
    cF
    fdm
    syl
    syl5sseq
    adantr
    @6
    @0
    cA
    @7
    f1ss
    syl2anc
    #
    @20
    @0
    @0
    @7
    crn
    #
    @14
    @8
    @35
    @0
    wceq
    #
    wph
    @5
    @8
    @6
    @0
    @7
    wfo
    @36
    @6
    @0
    @7
    f1ofo
    @6
    @0
    @7
    forn
    syl
    ad2antll
    syl5sseqr
    @23
    eqid
    gsumval3
    @20
    vk
    vx
    @21
    cB
    @22
    c1
    @4
    @20
    @4
    cn
    c1
    cuz
    cfv
    @29
    nnuz
    syl6eleq
    @20
    @6
    cB
    vk
    cv
    #
    @22
    @20
    @26
    @6
    cA
    @7
    wf
    #
    @6
    cB
    @22
    wf
    @27
    @20
    @32
    @38
    @34
    @6
    cA
    @7
    f1f
    syl
    @6
    cA
    cB
    cF
    @7
    fco
    syl2anc
    ffvelrnda
    @20
    @16
    @37
    cB
    wcel
    #
    vx
    cv
    #
    cB
    wcel
    #
    wa
    @37
    @40
    @21
    co
    cB
    wcel
    #
    @25
    @16
    @39
    @41
    @42
    cB
    @21
    cG
    @37
    @40
    gsumzcl.b
    @24
    mndcl
    3expb
    sylan
    seqcl
    eqeltrd
    expr
    exlimdv
    expimpd
    wph
    @0
    cfn
    wcel
    @1
    @10
    wo
    gsumzcl2.w
    @0
    vf
    fz1f1o
    syl
    mpjaod
end
