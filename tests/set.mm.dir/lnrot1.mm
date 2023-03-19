include "co.mm"
include "wcel.mm"
include "w3o.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "tgbtwncomb.mm"
include "biidd.mm"
include "3orbi123d.mm"
include "wb.mm"
include "3orrot.mm"
include "a1i.mm"
include "tgellng.mm"
include "3bitr4rd.mm"
include "bitr4d.mm"
include "mpbird.mm"

theorem lnrot1
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
  assume lnrot1.1: |- ( ph -> Y e. ( Z L X ) )
  assume lnrot1.2: |- ( ph -> Z =/= X )


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
    cY
    cZ
    cX
    cL
    co
    wcel
    #
    lnrot1.1
    wph
    @0
    cY
    cZ
    cX
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
    cX
    cZ
    cY
    cI
    co
    wcel
    #
    w3o
    #
    @1
    wph
    @3
    @4
    @2
    w3o
    #
    cZ
    cX
    cY
    cI
    co
    wcel
    #
    @4
    cY
    cX
    cZ
    cI
    co
    wcel
    #
    w3o
    @5
    @0
    wph
    @3
    @7
    @4
    @4
    @2
    @8
    wph
    cY
    cZ
    cX
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
    btwnlng1.z
    btwnlng1.x
    tgbtwncomb
    wph
    @4
    biidd
    wph
    cZ
    cY
    cX
    cP
    cG
    cI
    @9
    btwnlng1.p
    @10
    btwnlng1.i
    btwnlng1.g
    btwnlng1.z
    btwnlng1.y
    btwnlng1.x
    tgbtwncomb
    3orbi123d
    @5
    @6
    wb
    wph
    @2
    @3
    @4
    3orrot
    a1i
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
    3bitr4rd
    wph
    cP
    cG
    cI
    cL
    cZ
    cX
    cY
    btwnlng1.p
    btwnlng1.l
    btwnlng1.i
    btwnlng1.g
    btwnlng1.z
    btwnlng1.x
    lnrot1.2
    btwnlng1.y
    tgellng
    bitr4d
    mpbird
end
