include "co.mm"
include "cmpt.mm"
include "ccncf.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "wa.mm"
include "wral.mm"
include "cncff.mm"
include "syl.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "cc.mm"
include "wss.mm"
include "wb.mm"
include "ctx.mm"
include "ccn.mm"
include "a1i.mm"
include "ssid.mm"
include "cncfss.mm"
include "mp2an.mm"
include "sseldi.mm"
include "cncfmpt2f.mm"
include "cncffvrn.mm"
include "sylancr.mm"
include "mpbird.mm"

theorem cncfmpt2ss
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cJ: class J
  let cX: class X
  assume cncfmpt2ss.1: |- J = ( TopOpen ` CCfld )
  assume cncfmpt2ss.2: |- F e. ( ( J tX J ) Cn J )
  assume cncfmpt2ss.3: |- ( ph -> ( x e. X |-> A ) e. ( X -cn-> S ) )
  assume cncfmpt2ss.4: |- ( ph -> ( x e. X |-> B ) e. ( X -cn-> S ) )
  assume cncfmpt2ss.5: |- S C_ CC
  assume cncfmpt2ss.6: |- ( ( A e. S /\ B e. S ) -> ( A F B ) e. S )

  disjoint F x
  disjoint J x
  disjoint ph x
  disjoint S x
  disjoint X x
  assert |- ( ph -> ( x e. X |-> ( A F B ) ) e. ( X -cn-> S ) )

  proof
    wph
    vx
    cX
    cA
    cB
    cF
    co
    #
    cmpt
    #
    cX
    cS
    ccncf
    co
    #
    wcel
    #
    cX
    cS
    @1
    wf
    #
    wph
    vx
    cX
    @0
    cS
    @1
    wph
    vx
    cv
    cX
    wcel
    wa
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    @0
    cS
    wcel
    wph
    @5
    vx
    cX
    wph
    cX
    cS
    vx
    cX
    cA
    cmpt
    #
    wf
    #
    @5
    vx
    cX
    wral
    wph
    @7
    @2
    wcel
    @8
    cncfmpt2ss.3
    cX
    cS
    @7
    cncff
    syl
    vx
    cX
    cS
    cA
    @7
    @7
    eqid
    fmpt
    sylibr
    r19.21bi
    wph
    @6
    vx
    cX
    wph
    cX
    cS
    vx
    cX
    cB
    cmpt
    #
    wf
    #
    @6
    vx
    cX
    wral
    wph
    @9
    @2
    wcel
    @10
    cncfmpt2ss.4
    cX
    cS
    @9
    cncff
    syl
    vx
    cX
    cS
    cB
    @9
    @9
    eqid
    fmpt
    sylibr
    r19.21bi
    cncfmpt2ss.6
    syl2anc
    @1
    eqid
    fmptd
    wph
    cS
    cc
    wss
    #
    @1
    cX
    cc
    ccncf
    co
    #
    wcel
    @3
    @4
    wb
    cncfmpt2ss.5
    wph
    vx
    cA
    cB
    cF
    cJ
    cX
    cncfmpt2ss.1
    cF
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    wph
    cncfmpt2ss.2
    a1i
    wph
    @2
    @12
    @7
    @11
    cc
    cc
    wss
    @2
    @12
    wss
    cncfmpt2ss.5
    cc
    ssid
    cX
    cS
    cc
    cncfss
    mp2an
    #
    cncfmpt2ss.3
    sseldi
    wph
    @2
    @12
    @9
    @13
    cncfmpt2ss.4
    sseldi
    cncfmpt2f
    cX
    cc
    cS
    @1
    cncffvrn
    sylancr
    mpbird
end
