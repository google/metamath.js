include "cv.mm"
include "climc.mm"
include "co.mm"
include "wcel.mm"
include "wmo.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cnei.mm"
include "cfv.mm"
include "crest.mm"
include "cflf.mm"
include "cha.mm"
include "cfil.mm"
include "cc.mm"
include "wf.mm"
include "cnfldhaus.mm"
include "a1i.mm"
include "eqid.mm"
include "limcflflem.mm"
include "wss.mm"
include "difss.mm"
include "fssres.mm"
include "sylancl.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "hausflf.mm"
include "syl3anc.mm"
include "limcflf.mm"
include "eleq2d.mm"
include "mobidv.mm"
include "mpbird.mm"

theorem limcmo
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cK: class K
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let cC: class C
  let cL: class L
  assume limcflf.f: |- ( ph -> F : A --> CC )
  assume limcflf.a: |- ( ph -> A C_ CC )
  assume limcflf.b: |- ( ph -> B e. ( ( limPt ` K ) ` A ) )
  assume limcflf.k: |- K = ( TopOpen ` CCfld )

  disjoint B x
  disjoint F x
  disjoint K x
  disjoint A x
  disjoint ph x
  disjoint s t
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint B s
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint B t
  disjoint u w
  disjoint u x
  disjoint B u
  disjoint w x
  disjoint B w
  disjoint C s
  disjoint C t
  disjoint C u
  disjoint C w
  disjoint C x
  disjoint F s
  disjoint F t
  disjoint F u
  disjoint F w
  disjoint K s
  disjoint K t
  disjoint K u
  disjoint K w
  disjoint A t
  disjoint A u
  disjoint A w
  disjoint L s
  disjoint L u
  disjoint L x
  disjoint ph t
  disjoint ph u
  disjoint ph w
  assert |- ( ph -> E* x x e. ( F limCC B ) )

  proof
    wph
    vx
    cv
    #
    cF
    cB
    climc
    co
    #
    wcel
    #
    vx
    wmo
    @0
    cF
    cA
    cB
    csn
    #
    cdif
    #
    cres
    #
    cK
    @3
    cK
    cnei
    cfv
    cfv
    @4
    crest
    co
    #
    cflf
    co
    cfv
    #
    wcel
    #
    vx
    wmo
    #
    wph
    cK
    cha
    wcel
    #
    @6
    @4
    cfil
    cfv
    wcel
    @4
    cc
    @5
    wf
    #
    @9
    @10
    wph
    cK
    limcflf.k
    cnfldhaus
    a1i
    wph
    cA
    cB
    @4
    cF
    cK
    @6
    limcflf.f
    limcflf.a
    limcflf.b
    limcflf.k
    @4
    eqid
    #
    @6
    eqid
    #
    limcflflem
    wph
    cA
    cc
    cF
    wf
    @4
    cA
    wss
    @11
    limcflf.f
    cA
    @3
    difss
    cA
    cc
    @4
    cF
    fssres
    sylancl
    vx
    @5
    cK
    @6
    cc
    @4
    cc
    cK
    cK
    limcflf.k
    cnfldtopon
    toponunii
    hausflf
    syl3anc
    wph
    @2
    @8
    vx
    wph
    @1
    @7
    @0
    wph
    cA
    cB
    @4
    cF
    cK
    @6
    limcflf.f
    limcflf.a
    limcflf.b
    limcflf.k
    @12
    @13
    limcflf
    eleq2d
    mobidv
    mpbird
end
