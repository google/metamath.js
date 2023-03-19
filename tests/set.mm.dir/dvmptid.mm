include "cv.mm"
include "c1.mm"
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
include "simpr.mm"
include "wa.mm"
include "1cnd.mm"
include "cmpt.mm"
include "cdv.mm"
include "co.mm"
include "cid.mm"
include "cres.mm"
include "csn.mm"
include "cxp.mm"
include "mptresid.mm"
include "oveq2i.mm"
include "dvid.mm"
include "fconstmpt.mm"
include "3eqtri.mm"
include "a1i.mm"
include "dvmptres3.mm"

theorem dvmptid
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let cA: class A
  assume dvmptid.1: |- ( ph -> S e. { RR , CC } )

  disjoint ph x
  disjoint S x
  disjoint A x
  assert |- ( ph -> ( S _D ( x e. S |-> x ) ) = ( x e. S |-> 1 ) )

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
    cc
    cc
    cS
    @1
    eqid
    #
    dvmptid.1
    @1
    cc
    ctopon
    cfv
    wcel
    cc
    @1
    wcel
    wph
    @1
    @2
    cnfldtopon
    cc
    @1
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
    @3
    dvmptid.1
    cS
    recnprss
    syl
    cS
    cc
    df-ss
    sylib
    wph
    @0
    cc
    wcel
    #
    simpr
    wph
    @4
    wa
    1cnd
    cc
    vx
    cc
    @0
    cmpt
    #
    cdv
    co
    #
    vx
    cc
    c1
    cmpt
    #
    wceq
    wph
    @6
    cc
    cid
    cc
    cres
    #
    cdv
    co
    cc
    c1
    csn
    cxp
    @7
    @5
    @8
    cc
    cdv
    vx
    cc
    mptresid
    oveq2i
    dvid
    vx
    cc
    c1
    fconstmpt
    3eqtri
    a1i
    dvmptres3
end
