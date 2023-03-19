include "cres.mm"
include "cdv.mm"
include "co.mm"
include "cnt.mm"
include "cfv.mm"
include "cc.mm"
include "wss.mm"
include "wf.mm"
include "wceq.mm"
include "dvres.mm"
include "syl22anc.mm"
include "wfn.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "oveq2d.mm"
include "ctop.mm"
include "wcel.mm"
include "cuni.mm"
include "ctopon.mm"
include "crest.mm"
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
include "3eqtr3d.mm"
include "reseq2d.mm"
include "ntrss2.mm"
include "eqsstr3d.mm"
include "sstrd.mm"
include "3eqtr4rd.mm"

theorem dvresntr
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume dvresntr.s: |- ( ph -> S C_ CC )
  assume dvresntr.x: |- ( ph -> X C_ S )
  assume dvresntr.f: |- ( ph -> F : X --> CC )
  assume dvresntr.j: |- J = ( K |`t S )
  assume dvresntr.k: |- K = ( TopOpen ` CCfld )
  assume dvresntr.i: |- ( ph -> ( ( int ` J ) ` X ) = Y )


  assert |- ( ph -> ( S _D F ) = ( S _D ( F |` Y ) ) )

  proof
    wph
    cS
    cF
    cX
    cres
    #
    cdv
    co
    #
    cS
    cF
    cdv
    co
    #
    cX
    cJ
    cnt
    cfv
    #
    cfv
    #
    cres
    #
    @2
    cS
    cF
    cY
    cres
    cdv
    co
    #
    wph
    cS
    cc
    wss
    #
    cX
    cc
    cF
    wf
    #
    cX
    cS
    wss
    #
    @9
    @1
    @5
    wceq
    dvresntr.s
    dvresntr.f
    dvresntr.x
    dvresntr.x
    cX
    cX
    cS
    cJ
    cF
    cK
    dvresntr.k
    dvresntr.j
    dvres
    syl22anc
    wph
    @0
    cF
    cS
    cdv
    wph
    @8
    cF
    cX
    wfn
    @0
    cF
    wceq
    dvresntr.f
    cX
    cc
    cF
    ffn
    cX
    cF
    fnresdm
    3syl
    oveq2d
    wph
    @2
    cY
    @3
    cfv
    #
    cres
    #
    @2
    cY
    cres
    @6
    @5
    wph
    @10
    cY
    @2
    wph
    @4
    @3
    cfv
    #
    @4
    @10
    cY
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
    @4
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
    dvresntr.j
    wph
    cK
    cc
    ctopon
    cfv
    wcel
    @7
    @18
    @16
    wcel
    cK
    dvresntr.k
    cnfldtopon
    dvresntr.s
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
    dvresntr.x
    wph
    @17
    cS
    @14
    wceq
    @19
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
    @4
    cY
    @3
    dvresntr.i
    fveq2d
    dvresntr.i
    3eqtr3d
    reseq2d
    wph
    @7
    @8
    @9
    cY
    cS
    wss
    @6
    @11
    wceq
    dvresntr.s
    dvresntr.f
    dvresntr.x
    wph
    cY
    cX
    cS
    wph
    cY
    @4
    cX
    dvresntr.i
    wph
    @13
    @15
    @4
    cX
    wss
    @20
    @21
    cX
    cJ
    @14
    @22
    ntrss2
    syl2anc
    eqsstr3d
    dvresntr.x
    sstrd
    cX
    cY
    cS
    cJ
    cF
    cK
    dvresntr.k
    dvresntr.j
    dvres
    syl22anc
    wph
    @4
    cY
    @2
    dvresntr.i
    reseq2d
    3eqtr4rd
    3eqtr3d
end
