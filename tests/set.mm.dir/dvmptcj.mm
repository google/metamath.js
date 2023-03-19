include "cr.mm"
include "ccj.mm"
include "cmpt.mm"
include "ccom.mm"
include "cdv.mm"
include "co.mm"
include "cfv.mm"
include "cc.mm"
include "wf.mm"
include "wss.mm"
include "wceq.mm"
include "eqid.mm"
include "fmptd.mm"
include "cdm.mm"
include "dmeqd.mm"
include "wcel.mm"
include "wral.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "syl.mm"
include "eqtrd.mm"
include "dvbsss.mm"
include "syl6eqssr.mm"
include "dvcj.mm"
include "syl2anc.mm"
include "cv.mm"
include "eqidd.mm"
include "cjf.mm"
include "a1i.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "oveq2d.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "dvmptcl.mm"
include "3eqtr3d.mm"

theorem dvmptcj
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cX: class X
  let vy: setvar y
  assume dvmptcj.a: |- ( ( ph /\ x e. X ) -> A e. CC )
  assume dvmptcj.b: |- ( ( ph /\ x e. X ) -> B e. V )
  assume dvmptcj.da: |- ( ph -> ( RR _D ( x e. X |-> A ) ) = ( x e. X |-> B ) )

  disjoint ph x
  disjoint V x
  disjoint X x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ph -> ( RR _D ( x e. X |-> ( * ` A ) ) ) = ( x e. X |-> ( * ` B ) ) )

  proof
    wph
    cr
    ccj
    vx
    cX
    cA
    cmpt
    #
    ccom
    #
    cdv
    co
    #
    ccj
    cr
    @0
    cdv
    co
    #
    ccom
    #
    cr
    vx
    cX
    cA
    ccj
    cfv
    #
    cmpt
    #
    cdv
    co
    vx
    cX
    cB
    ccj
    cfv
    #
    cmpt
    wph
    cX
    cc
    @0
    wf
    cX
    cr
    wss
    @2
    @4
    wceq
    wph
    vx
    cX
    cA
    cc
    @0
    dvmptcj.a
    @0
    eqid
    fmptd
    wph
    cX
    @3
    cdm
    #
    cr
    wph
    @8
    vx
    cX
    cB
    cmpt
    #
    cdm
    #
    cX
    wph
    @3
    @9
    dvmptcj.da
    dmeqd
    wph
    cB
    cV
    wcel
    #
    vx
    cX
    wral
    @10
    cX
    wceq
    wph
    @11
    vx
    cX
    dvmptcj.b
    ralrimiva
    vx
    cX
    cB
    cV
    dmmptg
    syl
    eqtrd
    cr
    @0
    dvbsss
    syl6eqssr
    @0
    cX
    dvcj
    syl2anc
    wph
    @1
    @6
    cr
    cdv
    wph
    vx
    vy
    cX
    cc
    cA
    vy
    cv
    #
    ccj
    cfv
    #
    @5
    @0
    ccj
    dvmptcj.a
    wph
    @0
    eqidd
    wph
    vy
    cc
    cc
    ccj
    cc
    cc
    ccj
    wf
    wph
    cjf
    a1i
    feqmptd
    #
    @12
    cA
    ccj
    fveq2
    fmptco
    oveq2d
    wph
    vx
    vy
    cX
    cc
    cB
    @13
    @7
    @3
    ccj
    wph
    vx
    cA
    cB
    cr
    cV
    cX
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    dvmptcj.a
    dvmptcj.b
    dvmptcj.da
    dvmptcl
    dvmptcj.da
    @14
    @12
    cB
    ccj
    fveq2
    fmptco
    3eqtr3d
end
