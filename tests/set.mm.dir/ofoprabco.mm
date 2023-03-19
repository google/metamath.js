include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "co.mm"
include "ccom.mm"
include "cof.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cxp.mm"
include "ffvelrnda.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "fvmpt2d.mm"
include "fveq2d.mm"
include "wceq.mm"
include "df-ov.mm"
include "a1i.mm"
include "cvv.mm"
include "cmpt2.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "3eqtr2d.mm"
include "mpteq2dva.mm"
include "wf.mm"
include "wral.mm"
include "ovex.mm"
include "rgen2w.mm"
include "eqid.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "feq1d.mm"
include "mpbiri.mm"
include "fmpt3d.mm"
include "fcomptf.mm"
include "feqmptd.mm"
include "offval2.mm"
include "3eqtr4rd.mm"

theorem ofoprabco
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  let va: setvar a
  assume ofoprabco.1: |- F/_ a M
  assume ofoprabco.2: |- ( ph -> F : A --> B )
  assume ofoprabco.3: |- ( ph -> G : A --> C )
  assume ofoprabco.4: |- ( ph -> A e. V )
  assume ofoprabco.5: |- ( ph -> M = ( a e. A |-> <. ( F ` a ) , ( G ` a ) >. ) )
  assume ofoprabco.6: |- ( ph -> N = ( x e. B , y e. C |-> ( x R y ) ) )

  disjoint a x
  disjoint a y
  disjoint A a
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B a
  disjoint B x
  disjoint B y
  disjoint C a
  disjoint C x
  disjoint C y
  disjoint F a
  disjoint F x
  disjoint F y
  disjoint G a
  disjoint G x
  disjoint G y
  disjoint N a
  disjoint R a
  disjoint R x
  disjoint R y
  disjoint a ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( F oF R G ) = ( N o. M ) )

  proof
    wph
    va
    cA
    va
    cv
    #
    cM
    cfv
    #
    cN
    cfv
    #
    cmpt
    #
    va
    cA
    @0
    cF
    cfv
    #
    @0
    cG
    cfv
    #
    cR
    co
    #
    cmpt
    cN
    cM
    ccom
    #
    cF
    cG
    cR
    cof
    co
    wph
    va
    cA
    @2
    @6
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @2
    @4
    @5
    cop
    #
    cN
    cfv
    #
    @4
    @5
    cN
    co
    #
    @6
    @9
    @1
    @10
    cN
    wph
    va
    cA
    @10
    cM
    cB
    cC
    cxp
    #
    ofoprabco.5
    @9
    @4
    cB
    wcel
    @5
    cC
    wcel
    @10
    @13
    wcel
    wph
    cA
    cB
    @0
    cF
    ofoprabco.2
    ffvelrnda
    #
    wph
    cA
    cC
    @0
    cG
    ofoprabco.3
    ffvelrnda
    #
    @4
    @5
    cB
    cC
    opelxpi
    syl2anc
    #
    fvmpt2d
    fveq2d
    @12
    @11
    wceq
    @9
    @4
    @5
    cN
    df-ov
    a1i
    @9
    vx
    vy
    @4
    @5
    cB
    cC
    vx
    cv
    #
    vy
    cv
    #
    cR
    co
    #
    @6
    cN
    cvv
    wph
    cN
    vx
    vy
    cB
    cC
    @19
    cmpt2
    #
    wceq
    @8
    ofoprabco.6
    adantr
    @9
    @17
    @4
    wceq
    #
    @18
    @5
    wceq
    #
    wa
    wa
    @17
    @4
    @18
    @5
    cR
    @9
    @21
    @22
    simprl
    @9
    @21
    @22
    simprr
    oveq12d
    @14
    @15
    @9
    @4
    @5
    cR
    ovexd
    ovmpt2d
    3eqtr2d
    mpteq2dva
    wph
    @13
    cvv
    cN
    wf
    #
    cA
    @13
    cM
    wf
    @7
    @3
    wceq
    wph
    @23
    @13
    cvv
    @20
    wf
    #
    @19
    cvv
    wcel
    #
    vy
    cC
    wral
    vx
    cB
    wral
    @24
    @25
    vx
    vy
    cB
    cC
    @17
    @18
    cR
    ovex
    rgen2w
    vx
    vy
    cB
    cC
    @19
    cvv
    @20
    @20
    eqid
    fmpt2
    mpbi
    wph
    @13
    cvv
    cN
    @20
    ofoprabco.6
    feq1d
    mpbiri
    wph
    va
    cA
    @10
    @13
    cM
    ofoprabco.5
    @16
    fmpt3d
    va
    cN
    cM
    cA
    @13
    cvv
    ofoprabco.1
    fcomptf
    syl2anc
    wph
    va
    cA
    @4
    @5
    cR
    cF
    cG
    cV
    cB
    cC
    ofoprabco.4
    @14
    @15
    wph
    va
    cA
    cB
    cF
    ofoprabco.2
    feqmptd
    wph
    va
    cA
    cC
    cG
    ofoprabco.3
    feqmptd
    offval2
    3eqtr4rd
end
