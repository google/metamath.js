include "cmpt.mm"
include "cres.mm"
include "cdv.mm"
include "co.mm"
include "cc.mm"
include "cr.mm"
include "cpr.mm"
include "wcel.mm"
include "wf.mm"
include "cdm.mm"
include "wceq.mm"
include "eqid.mm"
include "fmptd.mm"
include "dmeqd.mm"
include "dmmptd.mm"
include "eqtrd.mm"
include "dvres3a.mm"
include "syl22anc.mm"
include "cin.mm"
include "rescom.mm"
include "resres.mm"
include "eqtri.mm"
include "reseq2d.mm"
include "syl5eq.mm"
include "wfn.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "reseq1d.mm"
include "inss2.mm"
include "syl6eqssr.mm"
include "resmptd.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "wral.mm"
include "ralrimiva.mm"
include "fnmpt.mm"
include "eqtr4d.mm"

theorem dvmptres3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cJ: class J
  let cV: class V
  let cX: class X
  let cY: class Y
  assume dvmptres3.j: |- J = ( TopOpen ` CCfld )
  assume dvmptres3.s: |- ( ph -> S e. { RR , CC } )
  assume dvmptres3.x: |- ( ph -> X e. J )
  assume dvmptres3.y: |- ( ph -> ( S i^i X ) = Y )
  assume dvmptres3.a: |- ( ( ph /\ x e. X ) -> A e. CC )
  assume dvmptres3.b: |- ( ( ph /\ x e. X ) -> B e. V )
  assume dvmptres3.d: |- ( ph -> ( CC _D ( x e. X |-> A ) ) = ( x e. X |-> B ) )

  disjoint ph x
  disjoint X x
  disjoint Y x
  assert |- ( ph -> ( S _D ( x e. Y |-> A ) ) = ( x e. Y |-> B ) )

  proof
    wph
    cS
    vx
    cX
    cA
    cmpt
    #
    cS
    cres
    #
    cdv
    co
    #
    cc
    @0
    cdv
    co
    #
    cS
    cres
    #
    cS
    vx
    cY
    cA
    cmpt
    #
    cdv
    co
    vx
    cY
    cB
    cmpt
    #
    wph
    cS
    cr
    cc
    cpr
    wcel
    cX
    cc
    @0
    wf
    #
    cX
    cJ
    wcel
    @3
    cdm
    #
    cX
    wceq
    @2
    @4
    wceq
    dvmptres3.s
    wph
    vx
    cX
    cA
    cc
    @0
    dvmptres3.a
    @0
    eqid
    fmptd
    #
    dvmptres3.x
    wph
    @8
    vx
    cX
    cB
    cmpt
    #
    cdm
    cX
    wph
    @3
    @10
    dvmptres3.d
    dmeqd
    wph
    vx
    @10
    cX
    cB
    cV
    @10
    eqid
    #
    dvmptres3.b
    dmmptd
    eqtrd
    cX
    cS
    @0
    cJ
    dvmptres3.j
    dvres3a
    syl22anc
    wph
    @1
    @5
    cS
    cdv
    wph
    @0
    cX
    cres
    #
    cS
    cres
    #
    @0
    cY
    cres
    #
    @1
    @5
    wph
    @13
    @0
    cS
    cX
    cin
    #
    cres
    #
    @14
    @13
    @1
    cX
    cres
    @16
    @0
    cX
    cS
    rescom
    @0
    cS
    cX
    resres
    eqtri
    wph
    @15
    cY
    @0
    dvmptres3.y
    reseq2d
    syl5eq
    wph
    @12
    @0
    cS
    wph
    @7
    @0
    cX
    wfn
    @12
    @0
    wceq
    @9
    cX
    cc
    @0
    ffn
    cX
    @0
    fnresdm
    3syl
    reseq1d
    wph
    vx
    cX
    cY
    cA
    wph
    cY
    @15
    cX
    dvmptres3.y
    cS
    cX
    inss2
    syl6eqssr
    #
    resmptd
    3eqtr3d
    oveq2d
    wph
    @10
    cX
    cres
    #
    cS
    cres
    #
    @10
    cY
    cres
    #
    @4
    @6
    wph
    @19
    @10
    @15
    cres
    #
    @20
    @19
    @10
    cS
    cres
    cX
    cres
    @21
    @10
    cX
    cS
    rescom
    @10
    cS
    cX
    resres
    eqtri
    wph
    @15
    cY
    @10
    dvmptres3.y
    reseq2d
    syl5eq
    wph
    @18
    @3
    cS
    wph
    @18
    @10
    @3
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
    wfn
    @18
    @10
    wceq
    wph
    @22
    vx
    cX
    dvmptres3.b
    ralrimiva
    vx
    cX
    cB
    @10
    cV
    @11
    fnmpt
    cX
    @10
    fnresdm
    3syl
    dvmptres3.d
    eqtr4d
    reseq1d
    wph
    vx
    cX
    cY
    cB
    @17
    resmptd
    3eqtr3d
    3eqtr3d
end
