include "cmpt.mm"
include "cres.mm"
include "cdv.mm"
include "co.mm"
include "cnt.mm"
include "cfv.mm"
include "cc.mm"
include "wss.mm"
include "wf.mm"
include "wceq.mm"
include "cr.mm"
include "cpr.mm"
include "wcel.mm"
include "recnprss.mm"
include "syl.mm"
include "eqid.mm"
include "fmptd.mm"
include "cdm.mm"
include "dmeqd.mm"
include "wral.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "eqtrd.mm"
include "dvbsss.mm"
include "syl6eqssr.mm"
include "sstrd.mm"
include "dvres.mm"
include "syl22anc.mm"
include "resmptd.mm"
include "oveq2d.mm"
include "reseq1d.mm"
include "reseq2d.mm"
include "ctop.mm"
include "cuni.mm"
include "ctopon.mm"
include "crest.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "topontop.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "ntrss2.mm"
include "syl2anc.mm"
include "eqsstr3d.mm"
include "3eqtrd.mm"
include "3eqtr3d.mm"

theorem dvmptres2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cJ: class J
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let cW: class W
  assume dvmptadd.s: |- ( ph -> S e. { RR , CC } )
  assume dvmptadd.a: |- ( ( ph /\ x e. X ) -> A e. CC )
  assume dvmptadd.b: |- ( ( ph /\ x e. X ) -> B e. V )
  assume dvmptadd.da: |- ( ph -> ( S _D ( x e. X |-> A ) ) = ( x e. X |-> B ) )
  assume dvmptres2.z: |- ( ph -> Z C_ X )
  assume dvmptres2.j: |- J = ( K |`t S )
  assume dvmptres2.k: |- K = ( TopOpen ` CCfld )
  assume dvmptres2.i: |- ( ph -> ( ( int ` J ) ` Z ) = Y )

  disjoint ph x
  disjoint S x
  disjoint V x
  disjoint X x
  disjoint Y x
  disjoint Z x
  disjoint W x
  assert |- ( ph -> ( S _D ( x e. Z |-> A ) ) = ( x e. Y |-> B ) )

  proof
    wph
    cS
    vx
    cX
    cA
    cmpt
    #
    cZ
    cres
    #
    cdv
    co
    #
    cS
    @0
    cdv
    co
    #
    cZ
    cJ
    cnt
    cfv
    cfv
    #
    cres
    #
    cS
    vx
    cZ
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
    cc
    wss
    #
    cX
    cc
    @0
    wf
    cX
    cS
    wss
    cZ
    cS
    wss
    @2
    @5
    wceq
    wph
    cS
    cr
    cc
    cpr
    wcel
    @8
    dvmptadd.s
    cS
    recnprss
    syl
    #
    wph
    vx
    cX
    cA
    cc
    @0
    dvmptadd.a
    @0
    eqid
    fmptd
    wph
    cX
    @3
    cdm
    #
    cS
    wph
    @10
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
    @11
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
    @12
    cX
    wceq
    wph
    @13
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
    cS
    @0
    dvbsss
    syl6eqssr
    #
    wph
    cZ
    cX
    cS
    dvmptres2.z
    @14
    sstrd
    #
    cX
    cZ
    cS
    cJ
    @0
    cK
    dvmptres2.k
    dvmptres2.j
    dvres
    syl22anc
    wph
    @1
    @6
    cS
    cdv
    wph
    vx
    cX
    cZ
    cA
    dvmptres2.z
    resmptd
    oveq2d
    wph
    @5
    @11
    @4
    cres
    @11
    cY
    cres
    @7
    wph
    @3
    @11
    @4
    dvmptadd.da
    reseq1d
    wph
    @4
    cY
    @11
    dvmptres2.i
    reseq2d
    wph
    vx
    cX
    cY
    cB
    wph
    cY
    cZ
    cX
    wph
    cY
    @4
    cZ
    dvmptres2.i
    wph
    cJ
    ctop
    wcel
    #
    cZ
    cJ
    cuni
    #
    wss
    @4
    cZ
    wss
    wph
    cJ
    cS
    ctopon
    cfv
    #
    wcel
    #
    @16
    wph
    cJ
    cK
    cS
    crest
    co
    #
    @18
    dvmptres2.j
    wph
    cK
    cc
    ctopon
    cfv
    wcel
    @8
    @20
    @18
    wcel
    cK
    dvmptres2.k
    cnfldtopon
    @9
    cS
    cK
    cc
    resttopon
    sylancr
    syl5eqel
    #
    cS
    cJ
    topontop
    syl
    wph
    cZ
    cS
    @17
    @15
    wph
    @19
    cS
    @17
    wceq
    @21
    cS
    cJ
    toponuni
    syl
    sseqtrd
    cZ
    cJ
    @17
    @17
    eqid
    ntrss2
    syl2anc
    eqsstr3d
    dvmptres2.z
    sstrd
    resmptd
    3eqtrd
    3eqtr3d
end
