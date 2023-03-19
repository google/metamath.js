include "cmpt.mm"
include "ccom.mm"
include "cxko.mm"
include "co.mm"
include "ccn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "wral.mm"
include "ctopon.mm"
include "cfv.mm"
include "adantr.mm"
include "ctop.mm"
include "topontop.mm"
include "syl.mm"
include "ccmp.mm"
include "cnlly.mm"
include "nllytop.mm"
include "eqid.mm"
include "xkotopon.mm"
include "syl2anc.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "eqidd.mm"
include "fmptcof.mm"
include "mpteq2dva.mm"
include "cmpt2.mm"
include "ctx.mm"
include "xkococn.mm"
include "wceq.mm"
include "coeq1.mm"
include "coeq2.mm"
include "sylan9eq.mm"
include "cnmpt12.mm"
include "eqeltrrd.mm"

theorem cnmptkk
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  assume cnmptkk.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmptkk.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmptkk.l: |- ( ph -> L e. ( TopOn ` Z ) )
  assume cnmptkk.m: |- ( ph -> M e. ( TopOn ` W ) )
  assume cnmptkk.n: |- ( ph -> L e. N-Locally Comp )
  assume cnmptkk.a: |- ( ph -> ( x e. X |-> ( y e. Y |-> A ) ) e. ( J Cn ( L ^ko K ) ) )
  assume cnmptkk.b: |- ( ph -> ( x e. X |-> ( z e. Z |-> B ) ) e. ( J Cn ( M ^ko L ) ) )
  assume cnmptkk.c: |- ( z = A -> B = C )

  disjoint A z
  disjoint B y
  disjoint K x
  disjoint L x
  disjoint x y
  disjoint X x
  disjoint X y
  disjoint J x
  disjoint M x
  disjoint ph x
  disjoint ph y
  disjoint Y y
  disjoint y z
  disjoint Z y
  disjoint Z z
  disjoint C z
  disjoint f g
  disjoint f z
  disjoint A f
  disjoint g z
  disjoint A g
  disjoint f y
  disjoint B f
  disjoint g y
  disjoint B g
  disjoint f x
  disjoint K f
  disjoint g x
  disjoint K g
  disjoint L f
  disjoint L g
  disjoint X f
  disjoint X g
  disjoint J f
  disjoint M f
  disjoint M g
  disjoint Y f
  disjoint Y g
  disjoint Z f
  disjoint Z g
  assert |- ( ph -> ( x e. X |-> ( y e. Y |-> C ) ) e. ( J Cn ( M ^ko K ) ) )

  proof
    wph
    vx
    cX
    vz
    cZ
    cB
    cmpt
    #
    vy
    cY
    cA
    cmpt
    #
    ccom
    #
    cmpt
    vx
    cX
    vy
    cY
    cC
    cmpt
    #
    cmpt
    cJ
    cM
    cK
    cxko
    co
    #
    ccn
    co
    wph
    vx
    cX
    @2
    @3
    wph
    vx
    cv
    cX
    wcel
    #
    wa
    #
    vy
    vz
    cY
    cZ
    cA
    cB
    cC
    @1
    @0
    @6
    cY
    cZ
    @1
    wf
    #
    cA
    cZ
    wcel
    vy
    cY
    wral
    @6
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cL
    cZ
    ctopon
    cfv
    wcel
    #
    @1
    cK
    cL
    ccn
    co
    #
    wcel
    #
    @7
    wph
    @8
    @5
    cnmptkk.k
    adantr
    wph
    @9
    @5
    cnmptkk.l
    adantr
    wph
    @11
    vx
    cX
    wph
    cX
    @10
    vx
    cX
    @1
    cmpt
    #
    wf
    #
    @11
    vx
    cX
    wral
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    cL
    cK
    cxko
    co
    #
    @10
    ctopon
    cfv
    wcel
    #
    @12
    cJ
    @14
    ccn
    co
    wcel
    @13
    cnmptkk.j
    wph
    cK
    ctop
    wcel
    #
    cL
    ctop
    wcel
    #
    @15
    wph
    @8
    @16
    cnmptkk.k
    cY
    cK
    topontop
    syl
    #
    wph
    cL
    ccmp
    cnlly
    wcel
    #
    @17
    cnmptkk.n
    ccmp
    cL
    nllytop
    syl
    #
    cK
    cL
    @14
    @14
    eqid
    xkotopon
    syl2anc
    #
    cnmptkk.a
    @12
    cJ
    @14
    cX
    @10
    cnf2
    syl3anc
    vx
    cX
    @10
    @1
    @12
    @12
    eqid
    fmpt
    sylibr
    r19.21bi
    @1
    cK
    cL
    cY
    cZ
    cnf2
    syl3anc
    vy
    cY
    cZ
    cA
    @1
    @1
    eqid
    fmpt
    sylibr
    @6
    @1
    eqidd
    @6
    @0
    eqidd
    cnmptkk.c
    fmptcof
    mpteq2dva
    wph
    vx
    vf
    vg
    @0
    @1
    vf
    cv
    #
    vg
    cv
    #
    ccom
    #
    @2
    cJ
    cM
    cL
    cxko
    co
    #
    @14
    @4
    cX
    cL
    cM
    ccn
    co
    #
    @10
    cnmptkk.j
    cnmptkk.b
    cnmptkk.a
    wph
    @17
    cM
    ctop
    wcel
    #
    @25
    @26
    ctopon
    cfv
    wcel
    @20
    wph
    cM
    cW
    ctopon
    cfv
    wcel
    @27
    cnmptkk.m
    cW
    cM
    topontop
    syl
    #
    cL
    cM
    @25
    @25
    eqid
    xkotopon
    syl2anc
    @21
    wph
    @16
    @19
    @27
    vf
    vg
    @26
    @10
    @24
    cmpt2
    #
    @25
    @14
    ctx
    co
    @4
    ccn
    co
    wcel
    @18
    cnmptkk.n
    @28
    cK
    cL
    cM
    vf
    vg
    @29
    @29
    eqid
    xkococn
    syl3anc
    @22
    @0
    wceq
    @23
    @1
    wceq
    @24
    @0
    @23
    ccom
    @2
    @22
    @0
    @23
    coeq1
    @23
    @1
    @0
    coeq2
    sylan9eq
    cnmpt12
    eqeltrrd
end
