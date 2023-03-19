include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "ciun.mm"
include "wcel.mm"
include "wrex.mm"
include "wa.mm"
include "simpr.mm"
include "clmod.mm"
include "cbs.mm"
include "adantr.mm"
include "eqid.mm"
include "lssel.mm"
include "sylan.mm"
include "lspsnid.mm"
include "syl2anc.mm"
include "weq.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "ex.mm"
include "lspsnel5a.mm"
include "sseld.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "eliun.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem lssats2
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let cU: class U
  let cN: class N
  let cW: class W
  let vy: setvar y
  assume lssats2.s: |- S = ( LSubSp ` W )
  assume lssats2.n: |- N = ( LSpan ` W )
  assume lssats2.w: |- ( ph -> W e. LMod )
  assume lssats2.u: |- ( ph -> U e. S )

  disjoint N x
  disjoint U x
  disjoint ph x
  disjoint x y
  disjoint N y
  disjoint U y
  disjoint ph y
  assert |- ( ph -> U = U_ x e. U ( N ` { x } ) )

  proof
    wph
    vy
    cU
    vx
    cU
    vx
    cv
    #
    csn
    #
    cN
    cfv
    #
    ciun
    #
    wph
    vy
    cv
    #
    cU
    wcel
    #
    @4
    @2
    wcel
    #
    vx
    cU
    wrex
    #
    @4
    @3
    wcel
    wph
    @5
    @7
    wph
    @5
    @7
    wph
    @5
    wa
    #
    @5
    @4
    @4
    csn
    #
    cN
    cfv
    #
    wcel
    #
    @7
    wph
    @5
    simpr
    @8
    cW
    clmod
    wcel
    #
    @4
    cW
    cbs
    cfv
    #
    wcel
    #
    @11
    wph
    @12
    @5
    lssats2.w
    adantr
    wph
    cU
    cS
    wcel
    #
    @5
    @14
    lssats2.u
    cS
    cU
    @13
    cW
    @4
    @13
    eqid
    #
    lssats2.s
    lssel
    sylan
    cN
    @13
    cW
    @4
    @16
    lssats2.n
    lspsnid
    syl2anc
    @6
    @11
    vx
    @4
    cU
    vx
    vy
    weq
    #
    @2
    @10
    @4
    @17
    @1
    @9
    cN
    @0
    @4
    sneq
    fveq2d
    eleq2d
    rspcev
    syl2anc
    ex
    wph
    @6
    @5
    vx
    cU
    wph
    @0
    cU
    wcel
    #
    wa
    #
    @2
    cU
    @4
    @19
    cS
    cU
    cN
    cW
    @0
    lssats2.s
    lssats2.n
    wph
    @12
    @18
    lssats2.w
    adantr
    wph
    @15
    @18
    lssats2.u
    adantr
    wph
    @18
    simpr
    lspsnel5a
    sseld
    rexlimdva
    impbid
    vx
    @4
    cU
    @2
    eliun
    syl6bbr
    eqrdv
end
