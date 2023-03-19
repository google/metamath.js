include "cmpt.mm"
include "cres.mm"
include "cdv.mm"
include "co.mm"
include "cnt.mm"
include "cfv.mm"
include "ctop.mm"
include "wcel.mm"
include "cuni.mm"
include "wss.mm"
include "wceq.mm"
include "ctopon.mm"
include "crest.mm"
include "cc.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "topontop.mm"
include "syl.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "ntridm.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "reseq2d.mm"
include "wf.mm"
include "fmptd.mm"
include "dvres.mm"
include "syl22anc.mm"
include "ntrss2.mm"
include "eqsstr3d.mm"
include "sstrd.mm"
include "3eqtr4d.mm"
include "ssid.mm"
include "resmpt.mm"
include "mp1i.mm"
include "oveq2d.mm"
include "resmptd.mm"

theorem dvmptntr
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  assume dvmptntr.s: |- ( ph -> S C_ CC )
  assume dvmptntr.x: |- ( ph -> X C_ S )
  assume dvmptntr.a: |- ( ( ph /\ x e. X ) -> A e. CC )
  assume dvmptntr.j: |- J = ( K |`t S )
  assume dvmptntr.k: |- K = ( TopOpen ` CCfld )
  assume dvmptntr.i: |- ( ph -> ( ( int ` J ) ` X ) = Y )

  disjoint ph x
  disjoint X x
  disjoint Y x
  assert |- ( ph -> ( S _D ( x e. X |-> A ) ) = ( S _D ( x e. Y |-> A ) ) )

  proof
    wph
    cS
    vx
    cX
    cA
    cmpt
    #
    cY
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
    cS
    vx
    cY
    cA
    cmpt
    #
    cdv
    co
    wph
    cS
    @0
    cX
    cres
    #
    cdv
    co
    #
    @2
    @3
    wph
    @3
    cX
    cJ
    cnt
    cfv
    #
    cfv
    #
    cres
    #
    @3
    cY
    @7
    cfv
    #
    cres
    #
    @6
    @2
    wph
    @8
    @10
    @3
    wph
    @8
    @7
    cfv
    #
    @8
    @10
    wph
    cJ
    ctop
    wcel
    #
    cX
    cJ
    cuni
    #
    wss
    #
    @12
    @8
    wceq
    wph
    cJ
    cS
    ctopon
    cfv
    #
    wcel
    #
    @13
    wph
    cJ
    cK
    cS
    crest
    co
    #
    @16
    dvmptntr.j
    wph
    cK
    cc
    ctopon
    cfv
    wcel
    cS
    cc
    wss
    #
    @18
    @16
    wcel
    cK
    dvmptntr.k
    cnfldtopon
    dvmptntr.s
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
    #
    wph
    cX
    cS
    @14
    dvmptntr.x
    wph
    @17
    cS
    @14
    wceq
    @20
    cS
    cJ
    toponuni
    syl
    sseqtrd
    #
    cX
    cJ
    @14
    @14
    eqid
    #
    ntridm
    syl2anc
    wph
    @8
    cY
    @7
    dvmptntr.i
    fveq2d
    eqtr3d
    reseq2d
    wph
    @19
    cX
    cc
    @0
    wf
    #
    cX
    cS
    wss
    #
    @25
    @6
    @9
    wceq
    dvmptntr.s
    wph
    vx
    cX
    cA
    cc
    @0
    dvmptntr.a
    @0
    eqid
    fmptd
    #
    dvmptntr.x
    dvmptntr.x
    cX
    cX
    cS
    cJ
    @0
    cK
    dvmptntr.k
    dvmptntr.j
    dvres
    syl22anc
    wph
    @19
    @24
    @25
    cY
    cS
    wss
    @2
    @11
    wceq
    dvmptntr.s
    @26
    dvmptntr.x
    wph
    cY
    cX
    cS
    wph
    cY
    @8
    cX
    dvmptntr.i
    wph
    @13
    @15
    @8
    cX
    wss
    @21
    @22
    cX
    cJ
    @14
    @23
    ntrss2
    syl2anc
    eqsstr3d
    #
    dvmptntr.x
    sstrd
    cX
    cY
    cS
    cJ
    @0
    cK
    dvmptntr.k
    dvmptntr.j
    dvres
    syl22anc
    3eqtr4d
    wph
    @5
    @0
    cS
    cdv
    cX
    cX
    wss
    @5
    @0
    wceq
    wph
    cX
    ssid
    vx
    cX
    cX
    cA
    resmpt
    mp1i
    oveq2d
    eqtr3d
    wph
    @1
    @4
    cS
    cdv
    wph
    vx
    cX
    cY
    cA
    @27
    resmptd
    oveq2d
    eqtr3d
end
