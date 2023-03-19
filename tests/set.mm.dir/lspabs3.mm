include "co.mm"
include "csn.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "clsm.mm"
include "clss.mm"
include "eqid.mm"
include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "csubg.mm"
include "lspsnsubg.mm"
include "eqeltrrd.mm"
include "lspsnid.mm"
include "lsmelvali.mm"
include "syl22anc.mm"
include "lspsnel5a.mm"
include "oveq2d.mm"
include "lsmidm.mm"
include "eqtr3d.mm"
include "sseqtrd.mm"
include "wne.mm"
include "cdif.mm"
include "lmodvacl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "lspsncmp.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem lspabs3
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
  assume lspabs3.y: |- ( ph -> Y e. V )
  assume lspabs3.xy: |- ( ph -> ( X .+ Y ) =/= .0. )
  assume lspabs3.e: |- ( ph -> ( N ` { X } ) = ( N ` { Y } ) )


  assert |- ( ph -> ( N ` { X } ) = ( N ` { ( X .+ Y ) } ) )

  proof
    wph
    cX
    cY
    c.pl
    co
    #
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
    @1
    @2
    wss
    @1
    @2
    wceq
    wph
    @1
    @2
    cY
    csn
    cN
    cfv
    #
    cW
    clsm
    cfv
    #
    co
    #
    @2
    wph
    cW
    clss
    cfv
    #
    @5
    cN
    cW
    @0
    @6
    eqid
    #
    lspabs2.n
    wph
    cW
    clvec
    wcel
    cW
    clmod
    wcel
    #
    lspabs2.w
    cW
    lveclmod
    syl
    #
    wph
    @8
    @2
    @6
    wcel
    #
    @3
    @6
    wcel
    #
    @5
    @6
    wcel
    @9
    wph
    @8
    cX
    cV
    wcel
    #
    @10
    @9
    lspabs2.x
    @6
    cN
    cV
    cW
    cX
    lspabs2.v
    @7
    lspabs2.n
    lspsncl
    syl2anc
    wph
    @8
    cY
    cV
    wcel
    #
    @11
    @9
    lspabs3.y
    @6
    cN
    cV
    cW
    cY
    lspabs2.v
    @7
    lspabs2.n
    lspsncl
    syl2anc
    @4
    @6
    @2
    @3
    cW
    @7
    @4
    eqid
    #
    lsmcl
    syl3anc
    wph
    @2
    cW
    csubg
    cfv
    #
    wcel
    #
    @3
    @15
    wcel
    cX
    @2
    wcel
    #
    cY
    @3
    wcel
    #
    @0
    @5
    wcel
    wph
    @8
    @12
    @16
    @9
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
    @2
    @3
    @15
    lspabs3.e
    @19
    eqeltrrd
    wph
    @8
    @12
    @17
    @9
    lspabs2.x
    cN
    cV
    cW
    cX
    lspabs2.v
    lspabs2.n
    lspsnid
    syl2anc
    wph
    @8
    @13
    @18
    @9
    lspabs3.y
    cN
    cV
    cW
    cY
    lspabs2.v
    lspabs2.n
    lspsnid
    syl2anc
    c.pl
    @4
    @2
    @3
    cW
    cX
    cY
    lspabs2.p
    @14
    lsmelvali
    syl22anc
    lspsnel5a
    wph
    @2
    @2
    @4
    co
    #
    @5
    @2
    wph
    @2
    @3
    @2
    @4
    lspabs3.e
    oveq2d
    wph
    @16
    @20
    @2
    wceq
    @19
    @4
    @2
    cW
    @14
    lsmidm
    syl
    eqtr3d
    sseqtrd
    wph
    cN
    cV
    cW
    @0
    cX
    c.0
    lspabs2.v
    lspabs2.o
    lspabs2.n
    lspabs2.w
    wph
    @0
    cV
    wcel
    #
    @0
    c.0
    wne
    @0
    cV
    c.0
    csn
    cdif
    wcel
    wph
    @8
    @12
    @13
    @21
    @9
    lspabs2.x
    lspabs3.y
    c.pl
    cV
    cW
    cX
    cY
    lspabs2.v
    lspabs2.p
    lmodvacl
    syl3anc
    lspabs3.xy
    @0
    cV
    c.0
    eldifsn
    sylanbrc
    lspabs2.x
    lspsncmp
    mpbid
    eqcomd
end
