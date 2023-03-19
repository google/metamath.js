include "cv.mm"
include "cur.mm"
include "cfv.mm"
include "cvsca.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "clmod.mm"
include "adantr.mm"
include "simpr.mm"
include "crg.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "asclfval.mm"
include "fmptd.mm"

theorem asclf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cK: class K
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume asclf.a: |- A = ( algSc ` W )
  assume asclf.f: |- F = ( Scalar ` W )
  assume asclf.r: |- ( ph -> W e. Ring )
  assume asclf.l: |- ( ph -> W e. LMod )
  assume asclf.k: |- K = ( Base ` F )
  assume asclf.b: |- B = ( Base ` W )


  assert |- ( ph -> A : K --> B )

  proof
    wph
    vx
    cK
    vx
    cv
    #
    cW
    cur
    cfv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    cB
    cA
    wph
    @0
    cK
    wcel
    #
    wa
    cW
    clmod
    wcel
    #
    @4
    @1
    cB
    wcel
    #
    @3
    cB
    wcel
    wph
    @5
    @4
    asclf.l
    adantr
    wph
    @4
    simpr
    wph
    @6
    @4
    wph
    cW
    crg
    wcel
    @6
    asclf.r
    cB
    cW
    @1
    asclf.b
    @1
    eqid
    #
    ringidcl
    syl
    adantr
    @0
    @2
    cF
    cK
    cB
    cW
    @1
    asclf.b
    asclf.f
    @2
    eqid
    #
    asclf.k
    lmodvscl
    syl3anc
    vx
    cA
    @2
    @1
    cF
    cK
    cW
    asclf.a
    asclf.f
    asclf.k
    @8
    @7
    asclfval
    fmptd
end
