include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cr.mm"
include "ccn.mm"
include "co.mm"
include "wf.mm"
include "ctop.mm"
include "syl6eleq.mm"
include "cntop1.mm"
include "syl.mm"
include "toptopon.mm"
include "sylib.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "retopon.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cnf2.mm"
include "syl3anc.mm"

theorem fcnre
  let wph: wff ph
  let cC: class C
  let cT: class T
  let cF: class F
  let cJ: class J
  let cK: class K
  assume fcnre.1: |- K = ( topGen ` ran (,) )
  assume fcnre.3: |- T = U. J
  assume sfcnre.5: |- C = ( J Cn K )
  assume fcnre.6: |- ( ph -> F e. C )


  assert |- ( ph -> F : T --> RR )

  proof
    wph
    cJ
    cT
    ctopon
    cfv
    wcel
    #
    cK
    cr
    ctopon
    cfv
    #
    wcel
    #
    cF
    cJ
    cK
    ccn
    co
    #
    wcel
    #
    cT
    cr
    cF
    wf
    wph
    cJ
    ctop
    wcel
    #
    @0
    wph
    @4
    @5
    wph
    cF
    cC
    @3
    fcnre.6
    sfcnre.5
    syl6eleq
    #
    cF
    cJ
    cK
    cntop1
    syl
    cJ
    cT
    fcnre.3
    toptopon
    sylib
    @2
    wph
    cK
    cioo
    crn
    ctg
    cfv
    @1
    fcnre.1
    retopon
    eqeltri
    a1i
    @6
    cF
    cJ
    cK
    cT
    cr
    cnf2
    syl3anc
end
