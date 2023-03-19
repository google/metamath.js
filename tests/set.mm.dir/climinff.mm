include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "nfci.mm"
include "nfral.mm"
include "nfrex.mm"
include "wb.mm"
include "breq2d.mm"
include "cbvral.mm"
include "a1i.mm"
include "rexbidv.mm"
include "imbi2d.mm"
include "climinf.mm"

theorem climinff
  let wph: wff ph
  let vx: setvar x
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  assume climinff.1: |- F/ k ph
  assume climinff.2: |- F/_ k F
  assume climinff.3: |- Z = ( ZZ>= ` M )
  assume climinff.4: |- ( ph -> M e. ZZ )
  assume climinff.5: |- ( ph -> F : Z --> RR )
  assume climinff.6: |- ( ( ph /\ k e. Z ) -> ( F ` ( k + 1 ) ) <_ ( F ` k ) )
  assume climinff.7: |- ( ph -> E. x e. RR A. k e. Z x <_ ( F ` k ) )

  disjoint k x
  disjoint F x
  disjoint Z k
  disjoint Z x
  disjoint j k
  disjoint j x
  disjoint j ph
  disjoint F j
  disjoint Z j
  assert |- ( ph -> F ~~> inf ( ran F , RR , < ) )

  proof
    wph
    vx
    vj
    cF
    cM
    cZ
    climinff.3
    climinff.4
    climinff.5
    wph
    vk
    cv
    #
    cZ
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
    @0
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    wph
    vj
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @7
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    vk
    vj
    @9
    @13
    vk
    wph
    @8
    vk
    climinff.1
    @8
    vk
    nfv
    #
    nfan
    vk
    @11
    @12
    cle
    vk
    @10
    cF
    climinff.2
    vk
    @10
    nfcv
    nffv
    vk
    cle
    nfcv
    #
    vk
    @7
    cF
    climinff.2
    vk
    @7
    nfcv
    nffv
    #
    nfbr
    nfim
    @0
    @7
    wceq
    #
    @2
    @9
    @6
    @13
    @17
    @1
    @8
    wph
    @0
    @7
    cZ
    eleq1
    anbi2d
    @17
    @4
    @11
    @5
    @12
    cle
    @17
    @3
    @10
    cF
    @0
    @7
    c1
    caddc
    oveq1
    fveq2d
    @0
    @7
    cF
    fveq2
    #
    breq12d
    imbi12d
    climinff.6
    chvar
    wph
    vx
    cv
    #
    @5
    cle
    wbr
    #
    vk
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    wi
    wph
    @19
    @12
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    wi
    vk
    vj
    wph
    @25
    vk
    climinff.1
    @24
    vk
    vx
    cr
    vk
    cr
    nfcv
    @23
    vk
    vj
    cZ
    vk
    vj
    cZ
    @14
    nfci
    vk
    @19
    @12
    cle
    vk
    @19
    nfcv
    @15
    @16
    nfbr
    #
    nfral
    nfrex
    nfim
    @17
    @22
    @25
    wph
    @17
    @21
    @24
    vx
    cr
    @21
    @24
    wb
    @17
    @20
    @23
    vk
    vj
    cZ
    @20
    vj
    nfv
    @26
    @17
    @5
    @12
    @19
    cle
    @18
    breq2d
    cbvral
    a1i
    rexbidv
    imbi2d
    climinff.7
    chvar
    climinf
end
