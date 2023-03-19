include "nfv.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "nfan.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfeq.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "limsupequzlem.mm"

theorem limsupequz
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cK: class K
  let cM: class M
  let cN: class N
  let vj: setvar j
  assume limsupequz.1: |- F/ k ph
  assume limsupequz.2: |- F/_ k F
  assume limsupequz.3: |- F/_ k G
  assume limsupequz.4: |- ( ph -> M e. ZZ )
  assume limsupequz.5: |- ( ph -> F Fn ( ZZ>= ` M ) )
  assume limsupequz.6: |- ( ph -> N e. ZZ )
  assume limsupequz.7: |- ( ph -> G Fn ( ZZ>= ` N ) )
  assume limsupequz.8: |- ( ph -> K e. ZZ )
  assume limsupequz.9: |- ( ( ph /\ k e. ( ZZ>= ` K ) ) -> ( F ` k ) = ( G ` k ) )

  disjoint K k
  disjoint F j
  disjoint G j
  disjoint K j
  disjoint j k
  disjoint M j
  disjoint N j
  disjoint j ph
  assert |- ( ph -> ( limsup ` F ) = ( limsup ` G ) )

  proof
    wph
    vj
    cF
    cG
    cK
    cM
    cN
    wph
    vj
    nfv
    limsupequz.4
    limsupequz.5
    limsupequz.6
    limsupequz.7
    limsupequz.8
    wph
    vk
    cv
    #
    cK
    cuz
    cfv
    #
    wcel
    #
    wa
    #
    @0
    cF
    cfv
    #
    @0
    cG
    cfv
    #
    wceq
    #
    wi
    wph
    vj
    cv
    #
    @1
    wcel
    #
    wa
    #
    @7
    cF
    cfv
    #
    @7
    cG
    cfv
    #
    wceq
    #
    wi
    vk
    vj
    @9
    @12
    vk
    wph
    @8
    vk
    limsupequz.1
    @8
    vk
    nfv
    nfan
    vk
    @10
    @11
    vk
    @7
    cF
    limsupequz.2
    vk
    @7
    nfcv
    #
    nffv
    vk
    @7
    cG
    limsupequz.3
    @13
    nffv
    nfeq
    nfim
    @0
    @7
    wceq
    #
    @3
    @9
    @6
    @12
    @14
    @2
    @8
    wph
    @0
    @7
    @1
    eleq1
    anbi2d
    @14
    @4
    @10
    @5
    @11
    @0
    @7
    cF
    fveq2
    @0
    @7
    cG
    fveq2
    eqeq12d
    imbi12d
    limsupequz.9
    chvar
    limsupequzlem
end
