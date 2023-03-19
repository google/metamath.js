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
include "eldifad.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "csubg.mm"
include "lsssssubg.mm"
include "sseldd.mm"
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

theorem mapdindp0
  let wph: wff ph
  let vw: setvar w
  let c.pl: class .+
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume mapdindp1.v: |- V = ( Base ` W )
  assume mapdindp1.p: |- .+ = ( +g ` W )
  assume mapdindp1.o: |- .0. = ( 0g ` W )
  assume mapdindp1.n: |- N = ( LSpan ` W )
  assume mapdindp1.w: |- ( ph -> W e. LVec )
  assume mapdindp1.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdindp1.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdindp1.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume mapdindp1.W: |- ( ph -> w e. ( V \ { .0. } ) )
  assume mapdindp1.e: |- ( ph -> ( N ` { Y } ) = ( N ` { Z } ) )
  assume mapdindp1.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume mapdindp1.f: |- ( ph -> -. w e. ( N ` { X , Y } ) )
  assume mapdindp1.yz: |- ( ph -> ( Y .+ Z ) =/= .0. )


  assert |- ( ph -> ( N ` { ( Y .+ Z ) } ) = ( N ` { Y } ) )

  proof
    wph
    cY
    cZ
    c.pl
    co
    #
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    wss
    @1
    @2
    wceq
    wph
    @1
    @2
    cZ
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
    mapdindp1.n
    wph
    cW
    clvec
    wcel
    cW
    clmod
    wcel
    #
    mapdindp1.w
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
    @5
    @6
    wcel
    @9
    wph
    @8
    cY
    cV
    wcel
    #
    @10
    @9
    wph
    cY
    cV
    c.0
    csn
    #
    mapdindp1.y
    eldifad
    #
    @6
    cN
    cV
    cW
    cY
    mapdindp1.v
    @7
    mapdindp1.n
    lspsncl
    syl2anc
    #
    wph
    @2
    @3
    @6
    mapdindp1.e
    @14
    eqeltrrd
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
    @16
    wcel
    cY
    @2
    wcel
    #
    cZ
    @3
    wcel
    #
    @0
    @5
    wcel
    wph
    @6
    @16
    @2
    wph
    @8
    @6
    @16
    wss
    @9
    @6
    cW
    @7
    lsssssubg
    syl
    @14
    sseldd
    #
    wph
    @2
    @3
    @16
    mapdindp1.e
    @20
    eqeltrrd
    wph
    @8
    @11
    @18
    @9
    @13
    cN
    cV
    cW
    cY
    mapdindp1.v
    mapdindp1.n
    lspsnid
    syl2anc
    wph
    @8
    cZ
    cV
    wcel
    #
    @19
    @9
    wph
    cZ
    cV
    @12
    mapdindp1.z
    eldifad
    #
    cN
    cV
    cW
    cZ
    mapdindp1.v
    mapdindp1.n
    lspsnid
    syl2anc
    c.pl
    @4
    @2
    @3
    cW
    cY
    cZ
    mapdindp1.p
    @15
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
    mapdindp1.e
    oveq2d
    wph
    @17
    @23
    @2
    wceq
    @20
    @4
    @2
    cW
    @15
    lsmidm
    syl
    eqtr3d
    sseqtrd
    wph
    cN
    cV
    cW
    @0
    cY
    c.0
    mapdindp1.v
    mapdindp1.o
    mapdindp1.n
    mapdindp1.w
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
    @12
    cdif
    wcel
    wph
    @8
    @11
    @21
    @24
    @9
    @13
    @22
    c.pl
    cV
    cW
    cY
    cZ
    mapdindp1.v
    mapdindp1.p
    lmodvacl
    syl3anc
    mapdindp1.yz
    @0
    cV
    c.0
    eldifsn
    sylanbrc
    @13
    lspsncmp
    mpbid
end
