include "cfv.mm"
include "cmpt.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "wa.mm"
include "cncff.mm"
include "syl.mm"
include "adantr.mm"
include "mptex2.mm"
include "ffvelrnd.mm"
include "eqid.mm"
include "fmptd.mm"
include "cc.mm"
include "wss.mm"
include "wb.mm"
include "cncfrss2.mm"
include "ccom.mm"
include "eqidd.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "ssid.mm"
include "cncfss.mm"
include "sylancl.mm"
include "sseldd.mm"
include "cncfco.mm"
include "eqeltrrd.mm"
include "cncffvrn.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem cncfcompt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vy: setvar y
  let vk: setvar k
  assume cncfcompt.bcn: |- ( ph -> ( x e. A |-> B ) e. ( A -cn-> C ) )
  assume cncfcompt.f: |- ( ph -> F e. ( C -cn-> D ) )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint F x
  disjoint ph x
  disjoint B y
  disjoint C y
  disjoint x y
  disjoint F y
  disjoint k x
  assert |- ( ph -> ( x e. A |-> ( F ` B ) ) e. ( A -cn-> D ) )

  proof
    wph
    vx
    cA
    cB
    cF
    cfv
    #
    cmpt
    #
    cA
    cD
    ccncf
    co
    wcel
    #
    cA
    cD
    @1
    wf
    #
    wph
    vx
    cA
    @0
    cD
    @1
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    cC
    cD
    cB
    cF
    wph
    cC
    cD
    cF
    wf
    #
    @4
    wph
    cF
    cC
    cD
    ccncf
    co
    #
    wcel
    #
    @5
    cncfcompt.f
    cC
    cD
    cF
    cncff
    syl
    #
    adantr
    wph
    vx
    cA
    cB
    cC
    wph
    vx
    cA
    cB
    cmpt
    #
    cA
    cC
    ccncf
    co
    wcel
    cA
    cC
    @9
    wf
    cncfcompt.bcn
    cA
    cC
    @9
    cncff
    syl
    mptex2
    #
    ffvelrnd
    @1
    eqid
    fmptd
    wph
    cD
    cc
    wss
    #
    @1
    cA
    cc
    ccncf
    co
    #
    wcel
    @2
    @3
    wb
    wph
    @7
    @11
    cncfcompt.f
    cC
    cD
    cF
    cncfrss2
    syl
    #
    wph
    cF
    @9
    ccom
    @1
    @12
    wph
    vx
    vy
    cA
    cC
    cB
    vy
    cv
    #
    cF
    cfv
    @0
    @9
    cF
    @10
    wph
    @9
    eqidd
    wph
    vy
    cC
    cD
    cF
    @8
    feqmptd
    @14
    cB
    cF
    fveq2
    fmptco
    wph
    cA
    cC
    cc
    @9
    cF
    cncfcompt.bcn
    wph
    @6
    cC
    cc
    ccncf
    co
    #
    cF
    wph
    @11
    cc
    cc
    wss
    @6
    @15
    wss
    @13
    cc
    ssid
    cC
    cD
    cc
    cncfss
    sylancl
    cncfcompt.f
    sseldd
    cncfco
    eqeltrrd
    cA
    cc
    cD
    @1
    cncffvrn
    syl2anc
    mpbird
end
