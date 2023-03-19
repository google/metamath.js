include "clss.mm"
include "cfv.mm"
include "csn.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "cun.mm"
include "elun2.mm"
include "nsyl.mm"
include "lssneln0.mm"

theorem hdmaplem3
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume hdmaplem1.v: |- V = ( Base ` W )
  assume hdmaplem1.n: |- N = ( LSpan ` W )
  assume hdmaplem1.w: |- ( ph -> W e. LMod )
  assume hdmaplem1.z: |- ( ph -> Z e. V )
  assume hdmaplem1.j: |- ( ph -> -. Z e. ( ( N ` { X } ) u. ( N ` { Y } ) ) )
  assume hdmaplem1.y: |- ( ph -> Y e. V )
  assume hdmaplem3.o: |- .0. = ( 0g ` W )


  assert |- ( ph -> Z e. ( V \ { .0. } ) )

  proof
    wph
    cW
    clss
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    cV
    cW
    cZ
    c.0
    hdmaplem1.v
    hdmaplem3.o
    @0
    eqid
    #
    hdmaplem1.w
    wph
    cW
    clmod
    wcel
    cY
    cV
    wcel
    @1
    @0
    wcel
    hdmaplem1.w
    hdmaplem1.y
    @0
    cN
    cV
    cW
    cY
    hdmaplem1.v
    @2
    hdmaplem1.n
    lspsncl
    syl2anc
    hdmaplem1.z
    wph
    cZ
    cX
    csn
    cN
    cfv
    #
    @1
    cun
    wcel
    cZ
    @1
    wcel
    hdmaplem1.j
    cZ
    @1
    @3
    elun2
    nsyl
    lssneln0
end
