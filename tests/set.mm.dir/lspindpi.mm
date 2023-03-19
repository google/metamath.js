include "csn.mm"
include "cfv.mm"
include "wne.mm"
include "cpr.mm"
include "wcel.mm"
include "wn.mm"
include "wceq.mm"
include "wss.mm"
include "clsm.mm"
include "co.mm"
include "csubg.mm"
include "clss.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "eqid.mm"
include "lsssssubg.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "lsmub1.mm"
include "lsmpr.mm"
include "sseqtr4d.mm"
include "sseq1.mm"
include "syl5ibrcom.mm"
include "lspprcl.mm"
include "lspsnel5.mm"
include "sylibrd.mm"
include "necon3bd.mm"
include "mpd.mm"
include "lsmub2.mm"
include "jca.mm"

theorem lspindpi
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume lspindpi.v: |- V = ( Base ` W )
  assume lspindpi.n: |- N = ( LSpan ` W )
  assume lspindpi.w: |- ( ph -> W e. LVec )
  assume lspindpi.x: |- ( ph -> X e. V )
  assume lspindpi.y: |- ( ph -> Y e. V )
  assume lspindpi.z: |- ( ph -> Z e. V )
  assume lspindpi.e: |- ( ph -> -. X e. ( N ` { Y , Z } ) )


  assert |- ( ph -> ( ( N ` { X } ) =/= ( N ` { Y } ) /\ ( N ` { X } ) =/= ( N ` { Z } ) ) )

  proof
    wph
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    wne
    #
    @0
    cZ
    csn
    cN
    cfv
    #
    wne
    #
    wph
    cX
    cY
    cZ
    cpr
    cN
    cfv
    #
    wcel
    #
    wn
    #
    @2
    lspindpi.e
    wph
    @6
    @0
    @1
    wph
    @0
    @1
    wceq
    #
    @0
    @5
    wss
    #
    @6
    wph
    @9
    @8
    @1
    @5
    wss
    wph
    @1
    @1
    @3
    cW
    clsm
    cfv
    #
    co
    #
    @5
    wph
    @1
    cW
    csubg
    cfv
    #
    wcel
    #
    @3
    @12
    wcel
    #
    @1
    @11
    wss
    wph
    cW
    clss
    cfv
    #
    @12
    @1
    wph
    cW
    clmod
    wcel
    #
    @15
    @12
    wss
    wph
    cW
    clvec
    wcel
    @16
    lspindpi.w
    cW
    lveclmod
    syl
    #
    @15
    cW
    @15
    eqid
    #
    lsssssubg
    syl
    #
    wph
    @16
    cY
    cV
    wcel
    @1
    @15
    wcel
    @17
    lspindpi.y
    @15
    cN
    cV
    cW
    cY
    lspindpi.v
    @18
    lspindpi.n
    lspsncl
    syl2anc
    sseldd
    #
    wph
    @15
    @12
    @3
    @19
    wph
    @16
    cZ
    cV
    wcel
    @3
    @15
    wcel
    @17
    lspindpi.z
    @15
    cN
    cV
    cW
    cZ
    lspindpi.v
    @18
    lspindpi.n
    lspsncl
    syl2anc
    sseldd
    #
    @10
    @1
    @3
    cW
    @10
    eqid
    #
    lsmub1
    syl2anc
    wph
    @10
    cN
    cV
    cW
    cY
    cZ
    lspindpi.v
    lspindpi.n
    @22
    @17
    lspindpi.y
    lspindpi.z
    lsmpr
    #
    sseqtr4d
    @0
    @1
    @5
    sseq1
    syl5ibrcom
    wph
    @15
    @5
    cN
    cV
    cW
    cX
    lspindpi.v
    @18
    lspindpi.n
    @17
    wph
    @15
    cN
    cV
    cW
    cY
    cZ
    lspindpi.v
    @18
    lspindpi.n
    @17
    lspindpi.y
    lspindpi.z
    lspprcl
    lspindpi.x
    lspsnel5
    #
    sylibrd
    necon3bd
    mpd
    wph
    @7
    @4
    lspindpi.e
    wph
    @6
    @0
    @3
    wph
    @0
    @3
    wceq
    #
    @9
    @6
    wph
    @9
    @25
    @3
    @5
    wss
    wph
    @3
    @11
    @5
    wph
    @13
    @14
    @3
    @11
    wss
    @20
    @21
    @10
    @1
    @3
    cW
    @22
    lsmub2
    syl2anc
    @23
    sseqtr4d
    @0
    @3
    @5
    sseq1
    syl5ibrcom
    @24
    sylibrd
    necon3bd
    mpd
    jca
end
