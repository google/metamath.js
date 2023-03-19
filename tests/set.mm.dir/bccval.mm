include "cc.mm"
include "cn0.mm"
include "cv.mm"
include "cfallfac.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "cbcc.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-bcc.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "ovexd.mm"
include "ovmpt2d.mm"

theorem bccval
  let wph: wff ph
  let cC: class C
  let cK: class K
  let vc: setvar c
  let vk: setvar k
  assume bccval.c: |- ( ph -> C e. CC )
  assume bccval.k: |- ( ph -> K e. NN0 )


  assert |- ( ph -> ( C _Cc K ) = ( ( C FallFac K ) / ( ! ` K ) ) )

  proof
    wph
    vc
    vk
    cC
    cK
    cc
    cn0
    vc
    cv
    #
    vk
    cv
    #
    cfallfac
    co
    #
    @1
    cfa
    cfv
    #
    cdiv
    co
    #
    cC
    cK
    cfallfac
    co
    #
    cK
    cfa
    cfv
    #
    cdiv
    co
    cbcc
    cvv
    cbcc
    vc
    vk
    cc
    cn0
    @4
    cmpt2
    wceq
    wph
    vk
    vc
    df-bcc
    a1i
    wph
    @0
    cC
    wceq
    #
    @1
    cK
    wceq
    #
    wa
    wa
    #
    @2
    @5
    @3
    @6
    cdiv
    @9
    @0
    cC
    @1
    cK
    cfallfac
    wph
    @7
    @8
    simprl
    wph
    @7
    @8
    simprr
    #
    oveq12d
    @9
    @1
    cK
    cfa
    @10
    fveq2d
    oveq12d
    bccval.c
    bccval.k
    wph
    @5
    @6
    cdiv
    ovexd
    ovmpt2d
end
