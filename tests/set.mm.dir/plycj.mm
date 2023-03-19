include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "cply.mm"
include "cfv.mm"
include "cc.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "ccj.mm"
include "ccoe.mm"
include "ccom.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "plycjlem.mm"
include "syl.mm"
include "wss.mm"
include "plybss.mm"
include "0cnd.mm"
include "snssd.mm"
include "unssd.mm"
include "cdgr.mm"
include "cn0.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "wa.mm"
include "wf.mm"
include "coef.mm"
include "elfznn0.mm"
include "fvco3.mm"
include "syl2an.mm"
include "ffvelrn.mm"
include "wi.mm"
include "wo.mm"
include "wral.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspccv.mm"
include "elsni.mm"
include "fveq2d.mm"
include "cj0.mm"
include "syl6eq.mm"
include "fvex.mm"
include "elsn.mm"
include "sylibr.mm"
include "a1i.mm"
include "orim12d.mm"
include "elun.mm"
include "3imtr4g.mm"
include "adantr.mm"
include "mpd.mm"
include "eqeltrd.mm"
include "elplyd.mm"
include "plyun0.mm"
include "syl6eleq.mm"

theorem plycj
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let cF: class F
  let cG: class G
  let cN: class N
  let vk: setvar k
  let vz: setvar z
  let cA: class A
  assume plycj.1: |- N = ( deg ` F )
  assume plycj.2: |- G = ( ( * o. F ) o. * )
  assume plycj.3: |- ( ( ph /\ x e. S ) -> ( * ` x ) e. S )
  assume plycj.4: |- ( ph -> F e. ( Poly ` S ) )

  disjoint F x
  disjoint N x
  disjoint ph x
  disjoint S x
  disjoint k x
  disjoint k z
  disjoint A k
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint F k
  disjoint F z
  disjoint N k
  disjoint N z
  disjoint k ph
  disjoint ph z
  disjoint S k
  disjoint S z
  assert |- ( ph -> G e. ( Poly ` S ) )

  proof
    wph
    cG
    cS
    cc0
    csn
    #
    cun
    #
    cply
    cfv
    #
    cS
    cply
    cfv
    #
    wph
    cG
    vz
    cc
    cc0
    cN
    cfz
    co
    #
    vk
    cv
    #
    ccj
    cF
    ccoe
    cfv
    #
    ccom
    cfv
    #
    vz
    cv
    @5
    cexp
    co
    cmul
    co
    vk
    csu
    cmpt
    #
    @2
    wph
    cF
    @3
    wcel
    #
    cG
    @8
    wceq
    plycj.4
    vz
    @6
    cS
    vk
    cF
    cG
    cN
    plycj.1
    plycj.2
    @6
    eqid
    #
    plycjlem
    syl
    wph
    vz
    @7
    @1
    vk
    cN
    wph
    cS
    @0
    cc
    wph
    @9
    cS
    cc
    wss
    plycj.4
    cS
    cF
    plybss
    syl
    wph
    cc0
    cc
    wph
    0cnd
    snssd
    unssd
    wph
    cN
    cF
    cdgr
    cfv
    #
    cn0
    plycj.1
    wph
    @9
    @11
    cn0
    wcel
    plycj.4
    cS
    cF
    dgrcl
    syl
    syl5eqel
    wph
    @5
    @4
    wcel
    #
    wa
    #
    @7
    @5
    @6
    cfv
    #
    ccj
    cfv
    #
    @1
    wph
    cn0
    @1
    @6
    wf
    #
    @5
    cn0
    wcel
    #
    @7
    @15
    wceq
    @12
    wph
    @9
    @16
    plycj.4
    @6
    cS
    cF
    @10
    coef
    syl
    #
    @5
    cN
    elfznn0
    #
    cn0
    @1
    @5
    ccj
    @6
    fvco3
    syl2an
    @13
    @14
    @1
    wcel
    #
    @15
    @1
    wcel
    #
    wph
    @16
    @17
    @20
    @12
    @18
    @19
    cn0
    @1
    @5
    @6
    ffvelrn
    syl2an
    wph
    @20
    @21
    wi
    @12
    wph
    @14
    cS
    wcel
    #
    @14
    @0
    wcel
    #
    wo
    @15
    cS
    wcel
    #
    @15
    @0
    wcel
    #
    wo
    @20
    @21
    wph
    @22
    @24
    @23
    @25
    wph
    vx
    cv
    #
    ccj
    cfv
    #
    cS
    wcel
    #
    vx
    cS
    wral
    @22
    @24
    wi
    wph
    @28
    vx
    cS
    plycj.3
    ralrimiva
    @28
    @24
    vx
    @14
    cS
    @26
    @14
    wceq
    @27
    @15
    cS
    @26
    @14
    ccj
    fveq2
    eleq1d
    rspccv
    syl
    @23
    @25
    wi
    wph
    @23
    @15
    cc0
    wceq
    @25
    @23
    @15
    cc0
    ccj
    cfv
    cc0
    @23
    @14
    cc0
    ccj
    @14
    cc0
    elsni
    fveq2d
    cj0
    syl6eq
    @15
    cc0
    @14
    ccj
    fvex
    elsn
    sylibr
    a1i
    orim12d
    @14
    cS
    @0
    elun
    @15
    cS
    @0
    elun
    3imtr4g
    adantr
    mpd
    eqeltrd
    elplyd
    eqeltrd
    cS
    plyun0
    syl6eleq
end
