include "cli.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cv.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "uzid.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "adantr.mm"
include "cc0.mm"
include "wceq.mm"
include "subidd.mm"
include "fveq2d.mm"
include "abs0.mm"
include "syl6eq.mm"
include "rpgt0.mm"
include "adantl.mm"
include "eqbrtrd.mm"
include "ralrimivw.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "cc.mm"
include "clim2c.mm"
include "mpbird.mm"

theorem climconst
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vj: setvar j
  let vx: setvar x
  assume climconst.1: |- Z = ( ZZ>= ` M )
  assume climconst.2: |- ( ph -> M e. ZZ )
  assume climconst.3: |- ( ph -> F e. V )
  assume climconst.4: |- ( ph -> A e. CC )
  assume climconst.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )

  disjoint A k
  disjoint F k
  disjoint k ph
  disjoint Z k
  disjoint j k
  disjoint j x
  disjoint A j
  disjoint k x
  disjoint A x
  disjoint F j
  disjoint F x
  disjoint M j
  disjoint j ph
  disjoint ph x
  disjoint Z j
  assert |- ( ph -> F ~~> A )

  proof
    wph
    cF
    cA
    cli
    wbr
    cA
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    wph
    @7
    vx
    crp
    wph
    @2
    crp
    wcel
    #
    wa
    #
    cM
    cZ
    wcel
    #
    @3
    vk
    cZ
    wral
    #
    @7
    wph
    @10
    @8
    wph
    cM
    cM
    cuz
    cfv
    #
    cZ
    wph
    cM
    cz
    wcel
    cM
    @12
    wcel
    climconst.2
    cM
    uzid
    syl
    climconst.1
    syl6eleqr
    adantr
    @9
    @3
    vk
    cZ
    @9
    @1
    cc0
    @2
    clt
    wph
    @1
    cc0
    wceq
    @8
    wph
    @1
    cc0
    cabs
    cfv
    cc0
    wph
    @0
    cc0
    cabs
    wph
    cA
    climconst.4
    subidd
    fveq2d
    abs0
    syl6eq
    adantr
    @8
    cc0
    @2
    clt
    wbr
    wph
    @2
    rpgt0
    adantl
    eqbrtrd
    ralrimivw
    @6
    @11
    vj
    cM
    cZ
    @4
    cM
    wceq
    #
    @3
    vk
    @5
    cZ
    @13
    @5
    @12
    cZ
    @4
    cM
    cuz
    fveq2
    climconst.1
    syl6eqr
    raleqdv
    rspcev
    syl2anc
    ralrimiva
    wph
    vx
    cA
    cA
    vj
    vk
    cF
    cM
    cV
    cZ
    climconst.1
    climconst.2
    climconst.3
    climconst.5
    climconst.4
    wph
    cA
    cc
    wcel
    vk
    cv
    cZ
    wcel
    climconst.4
    adantr
    clim2c
    mpbird
end
