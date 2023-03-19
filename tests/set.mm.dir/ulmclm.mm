include "culm.mm"
include "cfv.mm"
include "wbr.mm"
include "cli.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wral.mm"
include "cuz.mm"
include "wrex.mm"
include "crp.mm"
include "wcel.mm"
include "wi.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rspcv.mm"
include "syl.mm"
include "ralimdv.mm"
include "reximdv.mm"
include "cvv.mm"
include "wa.mm"
include "eqidd.mm"
include "cc.mm"
include "wf.mm"
include "ulmcl.mm"
include "ulmscl.mm"
include "ulm2.mm"
include "eqcomd.mm"
include "ffvelrnd.mm"
include "cmap.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "adantr.mm"
include "clim2c.mm"
include "3imtr4d.mm"
include "mpd.mm"

theorem ulmclm
  let wph: wff ph
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cW: class W
  let cZ: class Z
  let vj: setvar j
  let vx: setvar x
  let vz: setvar z
  assume ulmclm.z: |- Z = ( ZZ>= ` M )
  assume ulmclm.m: |- ( ph -> M e. ZZ )
  assume ulmclm.f: |- ( ph -> F : Z --> ( CC ^m S ) )
  assume ulmclm.a: |- ( ph -> A e. S )
  assume ulmclm.h: |- ( ph -> H e. W )
  assume ulmclm.e: |- ( ( ph /\ k e. Z ) -> ( ( F ` k ) ` A ) = ( H ` k ) )
  assume ulmclm.u: |- ( ph -> F ( ~~>u ` S ) G )

  disjoint A k
  disjoint F k
  disjoint G k
  disjoint k ph
  disjoint H k
  disjoint M k
  disjoint S k
  disjoint Z k
  disjoint j k
  disjoint j x
  disjoint j z
  disjoint A j
  disjoint k x
  disjoint k z
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint F j
  disjoint F x
  disjoint F z
  disjoint G j
  disjoint G x
  disjoint G z
  disjoint j ph
  disjoint ph x
  disjoint ph z
  disjoint H j
  disjoint H x
  disjoint M j
  disjoint M x
  disjoint M z
  disjoint S j
  disjoint S x
  disjoint S z
  disjoint Z j
  disjoint Z x
  assert |- ( ph -> H ~~> ( G ` A ) )

  proof
    wph
    cF
    cG
    cS
    culm
    cfv
    wbr
    #
    cH
    cA
    cG
    cfv
    #
    cli
    wbr
    #
    ulmclm.u
    wph
    vz
    cv
    #
    vk
    cv
    #
    cF
    cfv
    #
    cfv
    #
    @3
    cG
    cfv
    #
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
    vz
    cS
    wral
    #
    vk
    vj
    cv
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
    cA
    @5
    cfv
    #
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    @10
    clt
    wbr
    #
    vk
    @13
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    @0
    @2
    wph
    @15
    @21
    vx
    crp
    wph
    @14
    @20
    vj
    cZ
    wph
    @12
    @19
    vk
    @13
    wph
    cA
    cS
    wcel
    #
    @12
    @19
    wi
    ulmclm.a
    @11
    @19
    vz
    cA
    cS
    @3
    cA
    wceq
    #
    @9
    @18
    @10
    clt
    @23
    @8
    @17
    cabs
    @23
    @6
    @16
    @7
    @1
    cmin
    @3
    cA
    @5
    fveq2
    @3
    cA
    cG
    fveq2
    oveq12d
    fveq2d
    breq1d
    rspcv
    syl
    ralimdv
    reximdv
    ralimdv
    wph
    vx
    vz
    @7
    @6
    cS
    vj
    vk
    cF
    cG
    cM
    cvv
    cZ
    ulmclm.z
    ulmclm.m
    ulmclm.f
    wph
    @4
    cZ
    wcel
    #
    @3
    cS
    wcel
    #
    wa
    wa
    @6
    eqidd
    wph
    @25
    wa
    @7
    eqidd
    wph
    @0
    cS
    cc
    cG
    wf
    ulmclm.u
    cS
    cF
    cG
    ulmcl
    syl
    #
    wph
    @0
    cS
    cvv
    wcel
    ulmclm.u
    cS
    cF
    cG
    ulmscl
    syl
    ulm2
    wph
    vx
    @1
    @16
    vj
    vk
    cH
    cM
    cW
    cZ
    ulmclm.z
    ulmclm.m
    ulmclm.h
    wph
    @24
    wa
    #
    @16
    @4
    cH
    cfv
    ulmclm.e
    eqcomd
    wph
    cS
    cc
    cA
    cG
    @26
    ulmclm.a
    ffvelrnd
    @27
    cS
    cc
    cA
    @5
    @27
    @5
    cc
    cS
    cmap
    co
    #
    wcel
    cS
    cc
    @5
    wf
    wph
    cZ
    @28
    @4
    cF
    ulmclm.f
    ffvelrnda
    @5
    cc
    cS
    elmapi
    syl
    wph
    @22
    @24
    ulmclm.a
    adantr
    ffvelrnd
    clim2c
    3imtr4d
    mpd
end
