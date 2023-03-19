include "cv.mm"
include "c2.mm"
include "cvv.mm"
include "nfv.mm"
include "ctop.mm"
include "wcel.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "retop.mm"
include "eqeltri.mm"
include "a1i.mm"
include "salgencld.mm"
include "cr.mm"
include "reex.mm"
include "ssexd.mm"
include "wa.mm"
include "wss.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "2re.mm"
include "smfid.mm"
include "smfmulc1.mm"

theorem smf2id
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cJ: class J
  let vk: setvar k
  assume smf2id.j: |- J = ( topGen ` ran (,) )
  assume smf2id.b: |- B = ( SalGen ` J )
  assume smf2id.a: |- ( ph -> A C_ RR )

  disjoint A x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( x e. A |-> ( 2 x. x ) ) e. ( SMblFn ` B ) )

  proof
    wph
    vx
    cA
    vx
    cv
    #
    c2
    cB
    cvv
    wph
    vx
    nfv
    wph
    cB
    ctop
    cJ
    cJ
    ctop
    wcel
    wph
    cJ
    cioo
    crn
    ctg
    cfv
    ctop
    smf2id.j
    retop
    eqeltri
    a1i
    smf2id.b
    salgencld
    wph
    cA
    cr
    cvv
    cr
    cvv
    wcel
    wph
    reex
    a1i
    smf2id.a
    ssexd
    wph
    @0
    cA
    wcel
    #
    wa
    cA
    cr
    @0
    wph
    cA
    cr
    wss
    @1
    smf2id.a
    adantr
    wph
    @1
    simpr
    sseldd
    c2
    cr
    wcel
    wph
    2re
    a1i
    wph
    vx
    cA
    cB
    cJ
    smf2id.j
    smf2id.b
    smf2id.a
    smfid
    smfmulc1
end
