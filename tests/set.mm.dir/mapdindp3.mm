include "cv.mm"
include "co.mm"
include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wne.mm"
include "cpr.mm"
include "clmod.mm"
include "wss.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "eldifad.mm"
include "lspvadd.mm"
include "syl3anc.mm"
include "lspindp1.mm"
include "simprd.mm"
include "ssneldd.mm"
include "wceq.mm"
include "lspsnid.mm"
include "syl2anc.mm"
include "eleq2.mm"
include "syl5ibcom.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem mapdindp3
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


  assert |- ( ph -> ( N ` { X } ) =/= ( N ` { ( w .+ Y ) } ) )

  proof
    wph
    cX
    vw
    cv
    #
    cY
    c.pl
    co
    csn
    cN
    cfv
    #
    wcel
    #
    wn
    cX
    csn
    cN
    cfv
    #
    @1
    wne
    wph
    @1
    @0
    cY
    cpr
    cN
    cfv
    #
    cX
    wph
    cW
    clmod
    wcel
    #
    @0
    cV
    wcel
    cY
    cV
    wcel
    @1
    @4
    wss
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
    @0
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
    @7
    mapdindp1.y
    eldifad
    #
    c.pl
    cN
    cV
    cW
    @0
    cY
    mapdindp1.v
    mapdindp1.p
    mapdindp1.n
    lspvadd
    syl3anc
    wph
    @0
    csn
    cN
    cfv
    cY
    csn
    cN
    cfv
    wne
    cX
    @4
    wcel
    wn
    wph
    cN
    cV
    cW
    cX
    cY
    c.0
    @0
    mapdindp1.v
    mapdindp1.o
    mapdindp1.n
    mapdindp1.w
    mapdindp1.x
    @9
    @8
    mapdindp1.ne
    mapdindp1.f
    lspindp1
    simprd
    ssneldd
    wph
    @2
    @3
    @1
    wph
    cX
    @3
    wcel
    #
    @3
    @1
    wceq
    @2
    wph
    @5
    cX
    cV
    wcel
    @10
    @6
    wph
    cX
    cV
    @7
    mapdindp1.x
    eldifad
    cN
    cV
    cW
    cX
    mapdindp1.v
    mapdindp1.n
    lspsnid
    syl2anc
    @3
    @1
    cX
    eleq2
    syl5ibcom
    necon3bd
    mpd
end
