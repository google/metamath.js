include "ccl.mm"
include "cfv.mm"
include "cuni.mm"
include "ccld.mm"
include "wcel.mm"
include "wss.mm"
include "eqid.mm"
include "cldss.mm"
include "syl.mm"
include "ctopon.mm"
include "wceq.mm"
include "toponuni.mm"
include "sseqtr4d.mm"
include "lmcls.mm"
include "cldcls.mm"
include "eleqtrd.mm"

theorem lmcld
  let wph: wff ph
  let cP: class P
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vj: setvar j
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  assume lmff.1: |- Z = ( ZZ>= ` M )
  assume lmff.3: |- ( ph -> J e. ( TopOn ` X ) )
  assume lmff.4: |- ( ph -> M e. ZZ )
  assume lmcls.5: |- ( ph -> F ( ~~>t ` J ) P )
  assume lmcls.7: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. S )
  assume lmcld.8: |- ( ph -> S e. ( Clsd ` J ) )

  disjoint F k
  disjoint J k
  disjoint M k
  disjoint P k
  disjoint S k
  disjoint k ph
  disjoint X k
  disjoint Z k
  disjoint j k
  disjoint j u
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J j
  disjoint J u
  disjoint J x
  disjoint J y
  disjoint M j
  disjoint P j
  disjoint P u
  disjoint S u
  disjoint j ph
  disjoint ph u
  disjoint ph y
  disjoint X j
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint Z j
  disjoint Z u
  disjoint Z x
  assert |- ( ph -> P e. S )

  proof
    wph
    cP
    cS
    cJ
    ccl
    cfv
    cfv
    #
    cS
    wph
    cP
    cS
    vk
    cF
    cJ
    cM
    cX
    cZ
    lmff.1
    lmff.3
    lmff.4
    lmcls.5
    lmcls.7
    wph
    cS
    cJ
    cuni
    #
    cX
    wph
    cS
    cJ
    ccld
    cfv
    wcel
    #
    cS
    @1
    wss
    lmcld.8
    cS
    cJ
    @1
    @1
    eqid
    cldss
    syl
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    cX
    @1
    wceq
    lmff.3
    cX
    cJ
    toponuni
    syl
    sseqtr4d
    lmcls
    wph
    @2
    @0
    cS
    wceq
    lmcld.8
    cS
    cJ
    cldcls
    syl
    eleqtrd
end
