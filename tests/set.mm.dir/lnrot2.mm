include "co.mm"
include "wcel.mm"
include "w3o.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "tgbtwncomb.mm"
include "biidd.mm"
include "3orbi123d.mm"
include "3orrot.mm"
include "syl6bbr.mm"
include "tgellng.mm"
include "3bitr4d.mm"
include "mpbid.mm"

theorem lnrot2
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
  assume lnrot2.1: |- ( ph -> X e. ( Y L Z ) )
  assume lnrot2.2: |- ( ph -> Y =/= Z )


  assert |- ( ph -> Z e. ( X L Y ) )

  proof
    wph
    cX
    cY
    cZ
    cL
    co
    wcel
    #
    cZ
    cX
    cY
    cL
    co
    wcel
    #
    lnrot2.1
    wph
    cX
    cY
    cZ
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
    cZ
    cY
    cX
    cI
    co
    wcel
    #
    w3o
    #
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
    @3
    w3o
    #
    @0
    @1
    wph
    @5
    @7
    @3
    @6
    w3o
    @8
    wph
    @2
    @7
    @3
    @3
    @4
    @6
    wph
    cY
    cX
    cZ
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    btwnlng1.p
    @9
    eqid
    #
    btwnlng1.i
    btwnlng1.g
    btwnlng1.y
    btwnlng1.x
    btwnlng1.z
    tgbtwncomb
    wph
    @3
    biidd
    wph
    cY
    cZ
    cX
    cP
    cG
    cI
    @9
    btwnlng1.p
    @10
    btwnlng1.i
    btwnlng1.g
    btwnlng1.y
    btwnlng1.z
    btwnlng1.x
    tgbtwncomb
    3orbi123d
    @6
    @7
    @3
    3orrot
    syl6bbr
    wph
    cP
    cG
    cI
    cL
    cY
    cZ
    cX
    btwnlng1.p
    btwnlng1.l
    btwnlng1.i
    btwnlng1.g
    btwnlng1.y
    btwnlng1.z
    lnrot2.2
    btwnlng1.x
    tgellng
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
    3bitr4d
    mpbid
end
