include "ciun.mm"
include "cmpt.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "wral.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dfiun3g.mm"
include "syl.mm"
include "cpw.mm"
include "wss.mm"
include "eqid.mm"
include "rnmptss.mm"
include "cvv.mm"
include "wb.mm"
include "csalg.mm"
include "ssexd.mm"
include "elpwg.mm"
include "mpbird.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "1stcrestlem.mm"
include "salunicl.mm"
include "eqeltrd.mm"

theorem saliuncl
  let wph: wff ph
  let cS: class S
  let vk: setvar k
  let cE: class E
  let cK: class K
  let vx: setvar x
  assume saliuncl.s: |- ( ph -> S e. SAlg )
  assume saliuncl.kct: |- ( ph -> K ~<_ _om )
  assume saliuncl.b: |- ( ( ph /\ k e. K ) -> E e. S )

  disjoint K k
  disjoint S k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> U_ k e. K E e. S )

  proof
    wph
    vk
    cK
    cE
    ciun
    #
    vk
    cK
    cE
    cmpt
    #
    crn
    #
    cuni
    #
    cS
    wph
    cE
    cS
    wcel
    #
    vk
    cK
    wral
    #
    @0
    @3
    wceq
    wph
    @4
    vk
    cK
    saliuncl.b
    ralrimiva
    #
    vk
    cK
    cE
    cS
    dfiun3g
    syl
    wph
    cS
    @2
    saliuncl.s
    wph
    @2
    cS
    cpw
    wcel
    #
    @2
    cS
    wss
    #
    wph
    @5
    @8
    @6
    vk
    cK
    cE
    cS
    @1
    @1
    eqid
    rnmptss
    syl
    #
    wph
    @2
    cvv
    wcel
    @7
    @8
    wb
    wph
    @2
    cS
    csalg
    saliuncl.s
    @9
    ssexd
    @2
    cS
    cvv
    elpwg
    syl
    mpbird
    wph
    cK
    com
    cdom
    wbr
    @2
    com
    cdom
    wbr
    saliuncl.kct
    vk
    cK
    cE
    1stcrestlem
    syl
    salunicl
    eqeltrd
end
