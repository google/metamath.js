include "cc0.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "cr.mm"
include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "adantr.mm"
include "wa.mm"
include "0red.mm"
include "dvmptc.mm"
include "ctopon.mm"
include "wss.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "wceq.mm"
include "wi.mm"
include "wo.mm"
include "ax-resscn.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "eqimss.mm"
include "pm3.2i.mm"
include "cpr.mm"
include "elpri.mm"
include "syl.mm"
include "pm3.44.mm"
include "mpsyl.mm"
include "resttopon.mm"
include "syl2anc.mm"
include "toponss.mm"
include "dvmptres.mm"

theorem dvmptconst
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  assume dvmptconst.s: |- ( ph -> S e. { RR , CC } )
  assume dvmptconst.a: |- ( ph -> A e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume dvmptconst.b: |- ( ph -> B e. CC )

  disjoint A x
  disjoint B x
  disjoint S x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( S _D ( x e. A |-> B ) ) = ( x e. A |-> 0 ) )

  proof
    wph
    vx
    cB
    cc0
    cS
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    @0
    cr
    cS
    cA
    dvmptconst.s
    wph
    cB
    cc
    wcel
    vx
    cv
    cS
    wcel
    #
    dvmptconst.b
    adantr
    wph
    @2
    wa
    0red
    wph
    vx
    cB
    cS
    dvmptconst.s
    dvmptconst.b
    dvmptc
    wph
    @1
    cS
    ctopon
    cfv
    wcel
    #
    cA
    @1
    wcel
    cA
    cS
    wss
    wph
    @0
    cc
    ctopon
    cfv
    wcel
    #
    cS
    cc
    wss
    #
    @3
    @4
    wph
    @0
    @0
    eqid
    #
    cnfldtopon
    a1i
    cS
    cr
    wceq
    #
    @5
    wi
    #
    cS
    cc
    wceq
    #
    @5
    wi
    #
    wa
    wph
    @7
    @9
    wo
    #
    @5
    @8
    @10
    @7
    @5
    cr
    cc
    wss
    ax-resscn
    cS
    cr
    cc
    sseq1
    mpbiri
    cS
    cc
    eqimss
    pm3.2i
    wph
    cS
    cr
    cc
    cpr
    wcel
    @11
    dvmptconst.s
    cS
    cr
    cc
    elpri
    syl
    @5
    @7
    @9
    pm3.44
    mpsyl
    cS
    @0
    cc
    resttopon
    syl2anc
    dvmptconst.a
    cA
    @1
    cS
    toponss
    syl2anc
    @1
    eqid
    @6
    dvmptconst.a
    dvmptres
end
