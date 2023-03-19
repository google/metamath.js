include "cress.mm"
include "co.mm"
include "cgsu.mm"
include "cbs.mm"
include "cfv.mm"
include "c0g.mm"
include "ccntz.mm"
include "eqid.mm"
include "csubmnd.mm"
include "wcel.mm"
include "cmnd.mm"
include "submmnd.mm"
include "syl.mm"
include "wf.mm"
include "wceq.mm"
include "submbas.mm"
include "feq3d.mm"
include "mpbid.mm"
include "crn.mm"
include "cin.mm"
include "wss.mm"
include "frn.mm"
include "ssind.mm"
include "resscntz.mm"
include "syl2anc.mm"
include "sseqtr4d.mm"
include "cfsupp.mm"
include "subm0.mm"
include "breqtrd.mm"
include "gsumzcl.mm"
include "gsumsubm.mm"
include "3eltr4d.mm"

theorem gsumzsubmcl
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cF: class F
  let cG: class G
  let cV: class V
  let c.0: class .0.
  let cZ: class Z
  assume gsumzsubmcl.0: |- .0. = ( 0g ` G )
  assume gsumzsubmcl.z: |- Z = ( Cntz ` G )
  assume gsumzsubmcl.g: |- ( ph -> G e. Mnd )
  assume gsumzsubmcl.a: |- ( ph -> A e. V )
  assume gsumzsubmcl.s: |- ( ph -> S e. ( SubMnd ` G ) )
  assume gsumzsubmcl.f: |- ( ph -> F : A --> S )
  assume gsumzsubmcl.c: |- ( ph -> ran F C_ ( Z ` ran F ) )
  assume gsumzsubmcl.w: |- ( ph -> F finSupp .0. )


  assert |- ( ph -> ( G gsum F ) e. S )

  proof
    wph
    cG
    cS
    cress
    co
    #
    cF
    cgsu
    co
    @0
    cbs
    cfv
    #
    cG
    cF
    cgsu
    co
    cS
    wph
    cA
    @1
    cF
    @0
    cV
    @0
    c0g
    cfv
    #
    @0
    ccntz
    cfv
    #
    @1
    eqid
    @2
    eqid
    @3
    eqid
    #
    wph
    cS
    cG
    csubmnd
    cfv
    #
    wcel
    #
    @0
    cmnd
    wcel
    gsumzsubmcl.s
    cS
    @0
    cG
    @0
    eqid
    #
    submmnd
    syl
    gsumzsubmcl.a
    wph
    cA
    cS
    cF
    wf
    #
    cA
    @1
    cF
    wf
    gsumzsubmcl.f
    wph
    cS
    @1
    cF
    cA
    wph
    @6
    cS
    @1
    wceq
    gsumzsubmcl.s
    cS
    @0
    cG
    @7
    submbas
    syl
    #
    feq3d
    mpbid
    wph
    cF
    crn
    #
    @10
    cZ
    cfv
    #
    cS
    cin
    #
    @10
    @3
    cfv
    #
    wph
    @10
    @11
    cS
    gsumzsubmcl.c
    wph
    @8
    @10
    cS
    wss
    #
    gsumzsubmcl.f
    cA
    cS
    cF
    frn
    syl
    #
    ssind
    wph
    @6
    @14
    @13
    @12
    wceq
    gsumzsubmcl.s
    @15
    cS
    @10
    cG
    @0
    @5
    @3
    cZ
    @7
    gsumzsubmcl.z
    @4
    resscntz
    syl2anc
    sseqtr4d
    wph
    cF
    c.0
    @2
    cfsupp
    gsumzsubmcl.w
    wph
    @6
    c.0
    @2
    wceq
    gsumzsubmcl.s
    cS
    @0
    cG
    c.0
    @7
    gsumzsubmcl.0
    subm0
    syl
    breqtrd
    gsumzcl
    wph
    cA
    cS
    cF
    cG
    @0
    cV
    gsumzsubmcl.a
    gsumzsubmcl.s
    gsumzsubmcl.f
    @7
    gsumsubm
    @9
    3eltr4d
end
