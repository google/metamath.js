include "csn.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "clsm.mm"
include "co.mm"
include "csubg.mm"
include "wcel.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lspsnsubg.mm"
include "syl2anc.mm"
include "eldifad.mm"
include "eqid.mm"
include "lsmub2.mm"
include "oveq2d.mm"
include "lsmidm.mm"
include "cpr.mm"
include "lspprabs.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "lsmpr.mm"
include "3eqtr3d.mm"
include "3eqtr3rd.mm"
include "sseqtrd.mm"
include "lspsncmp.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem lspabs2
  let wph: wff ph
  let c.pl: class .+
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lspabs2.v: |- V = ( Base ` W )
  assume lspabs2.p: |- .+ = ( +g ` W )
  assume lspabs2.o: |- .0. = ( 0g ` W )
  assume lspabs2.n: |- N = ( LSpan ` W )
  assume lspabs2.w: |- ( ph -> W e. LVec )
  assume lspabs2.x: |- ( ph -> X e. V )
  assume lspabs2.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lspabs2.e: |- ( ph -> ( N ` { X } ) = ( N ` { ( X .+ Y ) } ) )


  assert |- ( ph -> ( N ` { X } ) = ( N ` { Y } ) )

  proof
    wph
    cY
    csn
    cN
    cfv
    #
    cX
    csn
    cN
    cfv
    #
    wph
    @0
    @1
    wss
    @0
    @1
    wceq
    wph
    @0
    @1
    @0
    cW
    clsm
    cfv
    #
    co
    #
    @1
    wph
    @1
    cW
    csubg
    cfv
    #
    wcel
    #
    @0
    @4
    wcel
    #
    @0
    @3
    wss
    wph
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    @5
    wph
    cW
    clvec
    wcel
    @7
    lspabs2.w
    cW
    lveclmod
    syl
    #
    lspabs2.x
    cN
    cV
    cW
    cX
    lspabs2.v
    lspabs2.n
    lspsnsubg
    syl2anc
    #
    wph
    @7
    cY
    cV
    wcel
    #
    @6
    @9
    wph
    cY
    cV
    c.0
    csn
    lspabs2.y
    eldifad
    #
    cN
    cV
    cW
    cY
    lspabs2.v
    lspabs2.n
    lspsnsubg
    syl2anc
    @2
    @1
    @0
    cW
    @2
    eqid
    #
    lsmub2
    syl2anc
    wph
    @1
    @1
    @2
    co
    #
    @1
    cX
    cY
    c.pl
    co
    #
    csn
    cN
    cfv
    #
    @2
    co
    #
    @1
    @3
    wph
    @1
    @16
    @1
    @2
    lspabs2.e
    oveq2d
    wph
    @5
    @14
    @1
    wceq
    @10
    @2
    @1
    cW
    @13
    lsmidm
    syl
    wph
    cX
    @15
    cpr
    cN
    cfv
    cX
    cY
    cpr
    cN
    cfv
    @17
    @3
    wph
    c.pl
    cN
    cV
    cW
    cX
    cY
    lspabs2.v
    lspabs2.p
    lspabs2.n
    @9
    lspabs2.x
    @12
    lspprabs
    wph
    @2
    cN
    cV
    cW
    cX
    @15
    lspabs2.v
    lspabs2.n
    @13
    @9
    lspabs2.x
    wph
    @7
    @8
    @11
    @15
    cV
    wcel
    @9
    lspabs2.x
    @12
    c.pl
    cV
    cW
    cX
    cY
    lspabs2.v
    lspabs2.p
    lmodvacl
    syl3anc
    lsmpr
    wph
    @2
    cN
    cV
    cW
    cX
    cY
    lspabs2.v
    lspabs2.n
    @13
    @9
    lspabs2.x
    @12
    lsmpr
    3eqtr3d
    3eqtr3rd
    sseqtrd
    wph
    cN
    cV
    cW
    cY
    cX
    c.0
    lspabs2.v
    lspabs2.o
    lspabs2.n
    lspabs2.w
    lspabs2.y
    lspabs2.x
    lspsncmp
    mpbid
    eqcomd
end
