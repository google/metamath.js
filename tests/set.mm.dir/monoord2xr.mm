include "cv.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cxr.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfel.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1w.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "nfbr.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "monoord2xrv.mm"

theorem monoord2xr
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vj: setvar j
  assume monoord2xr.p: |- F/ k ph
  assume monoord2xr.k: |- F/_ k F
  assume monoord2xr.n: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume monoord2xr.x: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. RR* )
  assume monoord2xr.l: |- ( ( ph /\ k e. ( M ... ( N - 1 ) ) ) -> ( F ` ( k + 1 ) ) <_ ( F ` k ) )

  disjoint M k
  disjoint N k
  disjoint F j
  disjoint M j
  disjoint j k
  disjoint N j
  disjoint j ph
  assert |- ( ph -> ( F ` N ) <_ ( F ` M ) )

  proof
    wph
    vj
    cF
    cM
    cN
    monoord2xr.n
    wph
    vk
    cv
    #
    cM
    cN
    cfz
    co
    #
    wcel
    #
    wa
    #
    @0
    cF
    cfv
    #
    cxr
    wcel
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
    @6
    cF
    cfv
    #
    cxr
    wcel
    #
    wi
    vk
    vj
    @8
    @10
    vk
    wph
    @7
    vk
    monoord2xr.p
    @7
    vk
    nfv
    nfan
    vk
    @9
    cxr
    vk
    @6
    cF
    monoord2xr.k
    vk
    @6
    nfcv
    nffv
    #
    vk
    cxr
    nfcv
    nfel
    nfim
    @0
    @6
    wceq
    #
    @3
    @8
    @5
    @10
    @12
    @2
    @7
    wph
    vk
    vj
    @1
    eleq1w
    anbi2d
    @12
    @4
    @9
    cxr
    @0
    @6
    cF
    fveq2
    #
    eleq1d
    imbi12d
    monoord2xr.x
    chvar
    wph
    @0
    cM
    cN
    c1
    cmin
    co
    cfz
    co
    #
    wcel
    #
    wa
    #
    @0
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @4
    cle
    wbr
    #
    wi
    wph
    @6
    @14
    wcel
    #
    wa
    #
    @6
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @9
    cle
    wbr
    #
    wi
    vk
    vj
    @21
    @24
    vk
    wph
    @20
    vk
    monoord2xr.p
    @20
    vk
    nfv
    nfan
    vk
    @23
    @9
    cle
    vk
    @22
    cF
    monoord2xr.k
    vk
    @22
    nfcv
    nffv
    vk
    cle
    nfcv
    @11
    nfbr
    nfim
    @12
    @16
    @21
    @19
    @24
    @12
    @15
    @20
    wph
    vk
    vj
    @14
    eleq1w
    anbi2d
    @12
    @18
    @23
    @4
    @9
    cle
    @12
    @17
    @22
    cF
    @0
    @6
    c1
    caddc
    oveq1
    fveq2d
    @13
    breq12d
    imbi12d
    monoord2xr.l
    chvar
    monoord2xrv
end
