include "ccom.mm"
include "cvv.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "cc.mm"
include "ccncf.mm"
include "co.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "wss.mm"
include "cncfrss2.mm"
include "sselda.mm"
include "syldan.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fex.mm"
include "sylancl.mm"
include "coexg.mm"
include "syl2anc.mm"
include "crp.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cncfi.mm"
include "3expia.mm"
include "imp.mm"
include "wceq.mm"
include "fvco3.mm"
include "sylan.mm"
include "climcn1.mm"

theorem climcncf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x
  assume climcncf.1: |- Z = ( ZZ>= ` M )
  assume climcncf.2: |- ( ph -> M e. ZZ )
  assume climcncf.4: |- ( ph -> F e. ( A -cn-> B ) )
  assume climcncf.5: |- ( ph -> G : Z --> A )
  assume climcncf.6: |- ( ph -> G ~~> D )
  assume climcncf.7: |- ( ph -> D e. A )


  assert |- ( ph -> ( F o. G ) ~~> ( F ` D ) )

  proof
    wph
    vx
    vy
    vz
    cD
    cA
    vk
    cF
    cG
    cF
    cG
    ccom
    #
    cM
    cvv
    cZ
    climcncf.1
    climcncf.2
    climcncf.7
    wph
    vz
    cv
    #
    cA
    wcel
    @1
    cF
    cfv
    #
    cB
    wcel
    @2
    cc
    wcel
    wph
    cA
    cB
    @1
    cF
    wph
    cF
    cA
    cB
    ccncf
    co
    #
    wcel
    #
    cA
    cB
    cF
    wf
    climcncf.4
    cA
    cB
    cF
    cncff
    syl
    ffvelrnda
    wph
    cB
    cc
    @2
    wph
    @4
    cB
    cc
    wss
    climcncf.4
    cA
    cB
    cF
    cncfrss2
    syl
    sselda
    syldan
    climcncf.6
    wph
    @4
    cG
    cvv
    wcel
    #
    @0
    cvv
    wcel
    climcncf.4
    wph
    cZ
    cA
    cG
    wf
    #
    cZ
    cvv
    wcel
    @5
    climcncf.5
    cZ
    cM
    cuz
    cfv
    cvv
    climcncf.1
    cM
    cuz
    fvex
    eqeltri
    cZ
    cA
    cvv
    cG
    fex
    sylancl
    cF
    cG
    @3
    cvv
    coexg
    syl2anc
    wph
    vx
    cv
    #
    crp
    wcel
    #
    @1
    cD
    cmin
    co
    cabs
    cfv
    vy
    cv
    clt
    wbr
    @2
    cD
    cF
    cfv
    cmin
    co
    cabs
    cfv
    @7
    clt
    wbr
    wi
    vz
    cA
    wral
    vy
    crp
    wrex
    #
    wph
    @4
    cD
    cA
    wcel
    #
    @8
    @9
    wi
    climcncf.4
    climcncf.7
    @4
    @10
    @8
    @9
    vy
    vz
    cA
    cB
    cD
    @7
    cF
    cncfi
    3expia
    syl2anc
    imp
    wph
    cZ
    cA
    vk
    cv
    #
    cG
    climcncf.5
    ffvelrnda
    wph
    @6
    @11
    cZ
    wcel
    @11
    @0
    cfv
    @11
    cG
    cfv
    cF
    cfv
    wceq
    climcncf.5
    cZ
    cA
    @11
    cF
    cG
    fvco3
    sylan
    climcn1
end
