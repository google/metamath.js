include "cc.mm"
include "wcel.mm"
include "cmpt.mm"
include "wf.mm"
include "wral.mm"
include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "cr.mm"
include "cpr.mm"
include "dvfg.mm"
include "syl.mm"
include "dmeqd.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "eqtrd.mm"
include "feq2d.mm"
include "mpbid.mm"
include "feq1d.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"

theorem dvmptcl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cV: class V
  let cX: class X
  let cW: class W
  let cY: class Y
  let cZ: class Z
  assume dvmptadd.s: |- ( ph -> S e. { RR , CC } )
  assume dvmptadd.a: |- ( ( ph /\ x e. X ) -> A e. CC )
  assume dvmptadd.b: |- ( ( ph /\ x e. X ) -> B e. V )
  assume dvmptadd.da: |- ( ph -> ( S _D ( x e. X |-> A ) ) = ( x e. X |-> B ) )

  disjoint ph x
  disjoint S x
  disjoint V x
  disjoint X x
  disjoint W x
  disjoint Y x
  disjoint Z x
  assert |- ( ( ph /\ x e. X ) -> B e. CC )

  proof
    wph
    cB
    cc
    wcel
    #
    vx
    cX
    wph
    cX
    cc
    vx
    cX
    cB
    cmpt
    #
    wf
    #
    @0
    vx
    cX
    wral
    wph
    cX
    cc
    cS
    vx
    cX
    cA
    cmpt
    #
    cdv
    co
    #
    wf
    #
    @2
    wph
    @4
    cdm
    #
    cc
    @4
    wf
    #
    @5
    wph
    cS
    cr
    cc
    cpr
    wcel
    @7
    dvmptadd.s
    cS
    @3
    dvfg
    syl
    wph
    @6
    cX
    cc
    @4
    wph
    @6
    @1
    cdm
    #
    cX
    wph
    @4
    @1
    dvmptadd.da
    dmeqd
    wph
    cB
    cV
    wcel
    #
    vx
    cX
    wral
    @8
    cX
    wceq
    wph
    @9
    vx
    cX
    dvmptadd.b
    ralrimiva
    vx
    cX
    cB
    cV
    dmmptg
    syl
    eqtrd
    feq2d
    mpbid
    wph
    cX
    cc
    @4
    @1
    dvmptadd.da
    feq1d
    mpbid
    vx
    cX
    cc
    cB
    @1
    @1
    eqid
    fmpt
    sylibr
    r19.21bi
end
