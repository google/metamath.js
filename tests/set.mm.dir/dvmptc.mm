include "cc0.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "cc.mm"
include "eqid.mm"
include "ctopon.mm"
include "wcel.mm"
include "cnfldtopon.mm"
include "toponmax.mm"
include "mp1i.mm"
include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "cr.mm"
include "cpr.mm"
include "recnprss.mm"
include "syl.mm"
include "df-ss.mm"
include "sylib.mm"
include "cv.mm"
include "adantr.mm"
include "wa.mm"
include "0cnd.mm"
include "csn.mm"
include "cxp.mm"
include "cdv.mm"
include "co.mm"
include "cmpt.mm"
include "dvconst.mm"
include "fconstmpt.mm"
include "oveq2i.mm"
include "3eqtr3g.mm"
include "dvmptres3.mm"

theorem dvmptc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  assume dvmptid.1: |- ( ph -> S e. { RR , CC } )
  assume dvmptc.2: |- ( ph -> A e. CC )

  disjoint A x
  disjoint ph x
  disjoint S x
  assert |- ( ph -> ( S _D ( x e. S |-> A ) ) = ( x e. S |-> 0 ) )

  proof
    wph
    vx
    cA
    cc0
    cS
    ccnfld
    ctopn
    cfv
    #
    cc
    cc
    cS
    @0
    eqid
    #
    dvmptid.1
    @0
    cc
    ctopon
    cfv
    wcel
    cc
    @0
    wcel
    wph
    @0
    @1
    cnfldtopon
    cc
    @0
    toponmax
    mp1i
    wph
    cS
    cc
    wss
    #
    cS
    cc
    cin
    cS
    wceq
    wph
    cS
    cr
    cc
    cpr
    wcel
    @2
    dvmptid.1
    cS
    recnprss
    syl
    cS
    cc
    df-ss
    sylib
    wph
    cA
    cc
    wcel
    #
    vx
    cv
    cc
    wcel
    #
    dvmptc.2
    adantr
    wph
    @4
    wa
    0cnd
    wph
    cc
    cc
    cA
    csn
    cxp
    #
    cdv
    co
    #
    cc
    cc0
    csn
    cxp
    #
    cc
    vx
    cc
    cA
    cmpt
    #
    cdv
    co
    vx
    cc
    cc0
    cmpt
    wph
    @3
    @6
    @7
    wceq
    dvmptc.2
    cA
    dvconst
    syl
    @5
    @8
    cc
    cdv
    vx
    cc
    cA
    fconstmpt
    oveq2i
    vx
    cc
    cc0
    fconstmpt
    3eqtr3g
    dvmptres3
end
