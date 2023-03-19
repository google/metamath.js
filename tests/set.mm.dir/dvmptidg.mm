include "cv.mm"
include "c1.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "cr.mm"
include "cc.mm"
include "wceq.mm"
include "wss.mm"
include "wi.mm"
include "wa.mm"
include "wo.mm"
include "ax-resscn.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "eqimss.mm"
include "pm3.2i.mm"
include "cpr.mm"
include "wcel.mm"
include "elpri.mm"
include "syl.mm"
include "pm3.44.mm"
include "mpsyl.mm"
include "sselda.mm"
include "1red.mm"
include "dvmptid.mm"
include "ctopon.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "resttopon.mm"
include "syl2anc.mm"
include "toponss.mm"
include "dvmptres.mm"

theorem dvmptidg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let vk: setvar k
  assume dvmptidg.s: |- ( ph -> S e. { RR , CC } )
  assume dvmptidg.a: |- ( ph -> A e. ( ( TopOpen ` CCfld ) |`t S ) )

  disjoint A x
  disjoint S x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( S _D ( x e. A |-> x ) ) = ( x e. A |-> 1 ) )

  proof
    wph
    vx
    vx
    cv
    #
    c1
    cS
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    @1
    cr
    cS
    cA
    dvmptidg.s
    wph
    cS
    cc
    @0
    cS
    cr
    wceq
    #
    cS
    cc
    wss
    #
    wi
    #
    cS
    cc
    wceq
    #
    @4
    wi
    #
    wa
    wph
    @3
    @6
    wo
    #
    @4
    @5
    @7
    @3
    @4
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
    @8
    dvmptidg.s
    cS
    cr
    cc
    elpri
    syl
    @4
    @3
    @6
    pm3.44
    mpsyl
    #
    sselda
    wph
    @0
    cS
    wcel
    wa
    1red
    wph
    vx
    cS
    dvmptidg.s
    dvmptid
    wph
    @2
    cS
    ctopon
    cfv
    wcel
    #
    cA
    @2
    wcel
    cA
    cS
    wss
    wph
    @1
    cc
    ctopon
    cfv
    wcel
    #
    @4
    @10
    @11
    wph
    @1
    @1
    eqid
    #
    cnfldtopon
    a1i
    @9
    cS
    @1
    cc
    resttopon
    syl2anc
    dvmptidg.a
    cA
    @2
    cS
    toponss
    syl2anc
    @2
    eqid
    @12
    dvmptidg.a
    dvmptres
end
