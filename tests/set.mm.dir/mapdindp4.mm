include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wne.mm"
include "cpr.mm"
include "wcel.mm"
include "wn.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "eldifad.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "lspindpi.mm"
include "simprd.mm"
include "necomd.mm"
include "lspindp3.mm"
include "wceq.mm"
include "lmodcom.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "neeqtrrd.mm"
include "eqnetrrd.mm"
include "lspindp1.mm"
include "clsm.mm"
include "eqid.mm"
include "lsmpr.mm"
include "preq2d.mm"
include "lspprabs.mm"
include "3eqtr3rd.mm"
include "oveq1d.mm"
include "prcom.mm"
include "fveq2i.mm"
include "a1i.mm"
include "3eqtr3d.mm"
include "eqtrd.mm"
include "neleqtrrd.mm"

theorem mapdindp4
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


  assert |- ( ph -> -. Z e. ( N ` { X , ( w .+ Y ) } ) )

  proof
    wph
    cX
    csn
    cN
    cfv
    #
    vw
    cv
    #
    cY
    c.pl
    co
    #
    csn
    #
    cN
    cfv
    #
    wne
    cZ
    cX
    @2
    cpr
    cN
    cfv
    wcel
    wn
    wph
    cN
    cV
    cW
    cZ
    @2
    c.0
    cX
    mapdindp1.v
    mapdindp1.o
    mapdindp1.n
    mapdindp1.w
    mapdindp1.z
    wph
    cW
    clmod
    wcel
    #
    @1
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    @2
    cV
    wcel
    wph
    cW
    clvec
    wcel
    @5
    mapdindp1.w
    cW
    lveclmod
    syl
    #
    wph
    @1
    cV
    c.0
    csn
    #
    mapdindp1.W
    eldifad
    #
    wph
    cY
    cV
    @9
    mapdindp1.y
    eldifad
    #
    c.pl
    cV
    cW
    @1
    cY
    mapdindp1.v
    mapdindp1.p
    lmodvacl
    syl3anc
    #
    wph
    cX
    cV
    @9
    mapdindp1.x
    eldifad
    #
    wph
    cY
    csn
    cN
    cfv
    #
    cZ
    csn
    cN
    cfv
    #
    @4
    mapdindp1.e
    wph
    @14
    cY
    @1
    c.pl
    co
    #
    csn
    #
    cN
    cfv
    @4
    wph
    c.pl
    cN
    cV
    cW
    cY
    @1
    c.0
    mapdindp1.v
    mapdindp1.p
    mapdindp1.o
    mapdindp1.n
    mapdindp1.w
    @11
    mapdindp1.W
    wph
    @1
    csn
    cN
    cfv
    #
    @14
    wph
    @18
    @0
    wne
    @18
    @14
    wne
    #
    wph
    cN
    cV
    cW
    @1
    cX
    cY
    mapdindp1.v
    mapdindp1.n
    mapdindp1.w
    @10
    @13
    @11
    mapdindp1.f
    lspindpi
    simprd
    necomd
    lspindp3
    wph
    @3
    @17
    cN
    wph
    @2
    @16
    wph
    @5
    @6
    @7
    @2
    @16
    wceq
    @8
    @10
    @11
    c.pl
    cV
    cW
    @1
    cY
    mapdindp1.v
    mapdindp1.p
    lmodcom
    syl3anc
    sneqd
    fveq2d
    neeqtrrd
    eqnetrrd
    wph
    cZ
    @2
    cpr
    cN
    cfv
    #
    @1
    cY
    cpr
    #
    cN
    cfv
    #
    cX
    wph
    @19
    cX
    @22
    wcel
    wn
    wph
    cN
    cV
    cW
    cX
    cY
    c.0
    @1
    mapdindp1.v
    mapdindp1.o
    mapdindp1.n
    mapdindp1.w
    mapdindp1.x
    @11
    @10
    mapdindp1.ne
    mapdindp1.f
    lspindp1
    simprd
    wph
    @20
    @15
    @4
    cW
    clsm
    cfv
    #
    co
    #
    @22
    wph
    @23
    cN
    cV
    cW
    cZ
    @2
    mapdindp1.v
    mapdindp1.n
    @23
    eqid
    #
    @8
    wph
    cZ
    cV
    @9
    mapdindp1.z
    eldifad
    @12
    lsmpr
    wph
    @14
    @4
    @23
    co
    #
    cY
    @1
    cpr
    #
    cN
    cfv
    #
    @24
    @22
    wph
    cY
    @16
    cpr
    #
    cN
    cfv
    cY
    @2
    cpr
    #
    cN
    cfv
    @28
    @26
    wph
    @29
    @30
    cN
    wph
    @16
    @2
    cY
    wph
    @5
    @7
    @6
    @16
    @2
    wceq
    @8
    @11
    @10
    c.pl
    cV
    cW
    cY
    @1
    mapdindp1.v
    mapdindp1.p
    lmodcom
    syl3anc
    preq2d
    fveq2d
    wph
    c.pl
    cN
    cV
    cW
    cY
    @1
    mapdindp1.v
    mapdindp1.p
    mapdindp1.n
    @8
    @11
    @10
    lspprabs
    wph
    @23
    cN
    cV
    cW
    cY
    @2
    mapdindp1.v
    mapdindp1.n
    @25
    @8
    @11
    @12
    lsmpr
    3eqtr3rd
    wph
    @14
    @15
    @4
    @23
    mapdindp1.e
    oveq1d
    @28
    @22
    wceq
    wph
    @27
    @21
    cN
    cY
    @1
    prcom
    fveq2i
    a1i
    3eqtr3d
    eqtrd
    neleqtrrd
    lspindp1
    simprd
end
