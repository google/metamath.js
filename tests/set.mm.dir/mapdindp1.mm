include "csn.mm"
include "cfv.mm"
include "co.mm"
include "wne.mm"
include "wceq.mm"
include "wa.mm"
include "cdif.mm"
include "wcel.mm"
include "eldifsni.mm"
include "syl.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "lspsn0.mm"
include "eqeq2d.mm"
include "wb.mm"
include "eldifad.mm"
include "lspsneq0.mm"
include "syl2anc.mm"
include "bitrd.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "adantr.mm"
include "sneq.mm"
include "fveq2d.mm"
include "adantl.mm"
include "neeqtrrd.mm"
include "cv.mm"
include "cpr.mm"
include "wn.mm"
include "simpr.mm"
include "mapdindp0.mm"
include "pm2.61dane.mm"

theorem mapdindp1
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


  assert |- ( ph -> ( N ` { X } ) =/= ( N ` { ( Y .+ Z ) } ) )

  proof
    wph
    cX
    csn
    cN
    cfv
    #
    cY
    cZ
    c.pl
    co
    #
    csn
    #
    cN
    cfv
    #
    wne
    @1
    c.0
    wph
    @1
    c.0
    wceq
    #
    wa
    @0
    c.0
    csn
    #
    cN
    cfv
    #
    @3
    wph
    @0
    @6
    wne
    #
    @4
    wph
    @7
    cX
    c.0
    wne
    #
    wph
    cX
    cV
    @5
    cdif
    #
    wcel
    #
    @8
    mapdindp1.x
    cX
    cV
    c.0
    eldifsni
    syl
    wph
    @0
    @6
    cX
    c.0
    wph
    @0
    @6
    wceq
    @0
    @5
    wceq
    #
    cX
    c.0
    wceq
    #
    wph
    @6
    @5
    @0
    wph
    cW
    clmod
    wcel
    #
    @6
    @5
    wceq
    wph
    cW
    clvec
    wcel
    #
    @13
    mapdindp1.w
    cW
    lveclmod
    syl
    #
    cN
    cW
    c.0
    mapdindp1.o
    mapdindp1.n
    lspsn0
    syl
    eqeq2d
    wph
    @13
    cX
    cV
    wcel
    @11
    @12
    wb
    @15
    wph
    cX
    cV
    @5
    mapdindp1.x
    eldifad
    cN
    cV
    cW
    cX
    c.0
    mapdindp1.v
    mapdindp1.o
    mapdindp1.n
    lspsneq0
    syl2anc
    bitrd
    necon3bid
    mpbird
    adantr
    @4
    @3
    @6
    wceq
    wph
    @4
    @2
    @5
    cN
    @1
    c.0
    sneq
    fveq2d
    adantl
    neeqtrrd
    wph
    @1
    c.0
    wne
    #
    wa
    #
    @0
    cY
    csn
    cN
    cfv
    #
    @3
    wph
    @0
    @18
    wne
    @16
    mapdindp1.ne
    adantr
    #
    @17
    vw
    c.pl
    cN
    cV
    cW
    cX
    cY
    c.0
    cZ
    mapdindp1.v
    mapdindp1.p
    mapdindp1.o
    mapdindp1.n
    wph
    @14
    @16
    mapdindp1.w
    adantr
    wph
    @10
    @16
    mapdindp1.x
    adantr
    wph
    cY
    @9
    wcel
    @16
    mapdindp1.y
    adantr
    wph
    cZ
    @9
    wcel
    @16
    mapdindp1.z
    adantr
    wph
    vw
    cv
    #
    @9
    wcel
    @16
    mapdindp1.W
    adantr
    wph
    @18
    cZ
    csn
    cN
    cfv
    wceq
    @16
    mapdindp1.e
    adantr
    @19
    wph
    @20
    cX
    cY
    cpr
    cN
    cfv
    wcel
    wn
    @16
    mapdindp1.f
    adantr
    wph
    @16
    simpr
    mapdindp0
    neeqtrrd
    pm2.61dane
end
