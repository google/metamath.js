include "wbr.mm"
include "clat.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "lattr.mm"
include "syl13anc.mm"
include "mp2and.mm"

theorem lattrd
  let wph: wff ph
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume lattrd.b: |- B = ( Base ` K )
  assume lattrd.l: |- .<_ = ( le ` K )
  assume lattrd.1: |- ( ph -> K e. Lat )
  assume lattrd.2: |- ( ph -> X e. B )
  assume lattrd.3: |- ( ph -> Y e. B )
  assume lattrd.4: |- ( ph -> Z e. B )
  assume lattrd.5: |- ( ph -> X .<_ Y )
  assume lattrd.6: |- ( ph -> Y .<_ Z )


  assert |- ( ph -> X .<_ Z )

  proof
    wph
    cX
    cY
    c.le
    wbr
    #
    cY
    cZ
    c.le
    wbr
    #
    cX
    cZ
    c.le
    wbr
    #
    lattrd.5
    lattrd.6
    wph
    cK
    clat
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    @0
    @1
    wa
    @2
    wi
    lattrd.1
    lattrd.2
    lattrd.3
    lattrd.4
    cB
    cK
    c.le
    cX
    cY
    cZ
    lattrd.b
    lattrd.l
    lattr
    syl13anc
    mp2and
end
