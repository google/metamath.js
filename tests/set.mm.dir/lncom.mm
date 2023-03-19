include "co.mm"
include "wcel.mm"
include "w3o.mm"
include "3orcomb.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "tgbtwncomb.mm"
include "3orbi123d.mm"
include "syl5bb.mm"
include "tgellng.mm"
include "necomd.mm"
include "3bitr4d.mm"
include "mpbird.mm"

theorem lncom
  let wph: wff ph
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume btwnlng1.p: |- P = ( Base ` G )
  assume btwnlng1.i: |- I = ( Itv ` G )
  assume btwnlng1.l: |- L = ( LineG ` G )
  assume btwnlng1.g: |- ( ph -> G e. TarskiG )
  assume btwnlng1.x: |- ( ph -> X e. P )
  assume btwnlng1.y: |- ( ph -> Y e. P )
  assume btwnlng1.z: |- ( ph -> Z e. P )
  assume btwnlng1.d: |- ( ph -> X =/= Y )
  assume lncom.1: |- ( ph -> Z e. ( Y L X ) )


  assert |- ( ph -> Z e. ( X L Y ) )

  proof
    wph
    cZ
    cX
    cY
    cL
    co
    wcel
    #
    cZ
    cY
    cX
    cL
    co
    wcel
    #
    lncom.1
    wph
    cZ
    cX
    cY
    cI
    co
    wcel
    #
    cX
    cZ
    cY
    cI
    co
    wcel
    #
    cY
    cX
    cZ
    cI
    co
    wcel
    #
    w3o
    #
    cZ
    cY
    cX
    cI
    co
    wcel
    #
    cY
    cZ
    cX
    cI
    co
    wcel
    #
    cX
    cY
    cZ
    cI
    co
    wcel
    #
    w3o
    #
    @0
    @1
    @5
    @2
    @4
    @3
    w3o
    wph
    @9
    @2
    @3
    @4
    3orcomb
    wph
    @2
    @6
    @4
    @7
    @3
    @8
    wph
    cX
    cZ
    cY
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    btwnlng1.p
    @10
    eqid
    #
    btwnlng1.i
    btwnlng1.g
    btwnlng1.x
    btwnlng1.z
    btwnlng1.y
    tgbtwncomb
    wph
    cX
    cY
    cZ
    cP
    cG
    cI
    @10
    btwnlng1.p
    @11
    btwnlng1.i
    btwnlng1.g
    btwnlng1.x
    btwnlng1.y
    btwnlng1.z
    tgbtwncomb
    wph
    cZ
    cX
    cY
    cP
    cG
    cI
    @10
    btwnlng1.p
    @11
    btwnlng1.i
    btwnlng1.g
    btwnlng1.z
    btwnlng1.x
    btwnlng1.y
    tgbtwncomb
    3orbi123d
    syl5bb
    wph
    cP
    cG
    cI
    cL
    cX
    cY
    cZ
    btwnlng1.p
    btwnlng1.l
    btwnlng1.i
    btwnlng1.g
    btwnlng1.x
    btwnlng1.y
    btwnlng1.d
    btwnlng1.z
    tgellng
    wph
    cP
    cG
    cI
    cL
    cY
    cX
    cZ
    btwnlng1.p
    btwnlng1.l
    btwnlng1.i
    btwnlng1.g
    btwnlng1.y
    btwnlng1.x
    wph
    cX
    cY
    btwnlng1.d
    necomd
    btwnlng1.z
    tgellng
    3bitr4d
    mpbird
end
