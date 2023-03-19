include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cr.mm"
include "wcel.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wral.mm"
include "cmpt.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "elinel2.mm"
include "adantl.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "rge0ssre.mm"
include "wf.mm"
include "ad2antrr.mm"
include "elinel1.mm"
include "elpwi.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "adantll.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "fsumrecl.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "rnmptss.mm"

theorem sge0rnre
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cX: class X
  let vk: setvar k
  assume sge0rnre.1: |- ( ph -> F : X --> ( 0 [,) +oo ) )

  disjoint X x
  disjoint X y
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ran ( x e. ( ~P X i^i Fin ) |-> sum_ y e. x ( F ` y ) ) C_ RR )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cF
    cfv
    #
    vy
    csu
    #
    cr
    wcel
    #
    vx
    cX
    cpw
    #
    cfn
    cin
    #
    wral
    vx
    @6
    @3
    cmpt
    #
    crn
    cr
    wss
    wph
    @4
    vx
    @6
    wph
    @0
    @6
    wcel
    #
    wa
    #
    @0
    @2
    vy
    @8
    @0
    cfn
    wcel
    wph
    @0
    @5
    cfn
    elinel2
    adantl
    @9
    @1
    @0
    wcel
    #
    wa
    #
    cc0
    cpnf
    cico
    co
    #
    cr
    @2
    rge0ssre
    @11
    cX
    @12
    @1
    cF
    wph
    cX
    @12
    cF
    wf
    @8
    @10
    sge0rnre.1
    ad2antrr
    @8
    @10
    @1
    cX
    wcel
    wph
    @8
    @10
    wa
    @0
    cX
    @1
    @8
    @0
    cX
    wss
    #
    @10
    @8
    @0
    @5
    wcel
    @13
    @0
    @5
    cfn
    elinel1
    @0
    cX
    elpwi
    syl
    adantr
    @8
    @10
    simpr
    sseldd
    adantll
    ffvelrnd
    sseldi
    fsumrecl
    ralrimiva
    vx
    @6
    @3
    cr
    @7
    @7
    eqid
    rnmptss
    syl
end
