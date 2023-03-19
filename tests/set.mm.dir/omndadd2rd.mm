include "cpo.mm"
include "wcel.mm"
include "co.mm"
include "w3a.mm"
include "wbr.mm"
include "comnd.mm"
include "ctos.mm"
include "omndtos.mm"
include "tospos.mm"
include "3syl.mm"
include "cmnd.mm"
include "omndmnd.mm"
include "syl.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "3jca.mm"
include "coppg.mm"
include "cfv.mm"
include "omndaddr.mm"
include "syl131anc.mm"
include "omndadd.mm"
include "wa.mm"
include "postr.mm"
include "imp.mm"
include "syl22anc.mm"

theorem omndadd2rd
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let c.le: class .<_
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume omndadd.0: |- B = ( Base ` M )
  assume omndadd.1: |- .<_ = ( le ` M )
  assume omndadd.2: |- .+ = ( +g ` M )
  assume omndadd2d.m: |- ( ph -> M e. oMnd )
  assume omndadd2d.w: |- ( ph -> W e. B )
  assume omndadd2d.x: |- ( ph -> X e. B )
  assume omndadd2d.y: |- ( ph -> Y e. B )
  assume omndadd2d.z: |- ( ph -> Z e. B )
  assume omndadd2d.1: |- ( ph -> X .<_ Z )
  assume omndadd2d.2: |- ( ph -> Y .<_ W )
  assume omndadd2rd.c: |- ( ph -> ( oppG ` M ) e. oMnd )


  assert |- ( ph -> ( X .+ Y ) .<_ ( Z .+ W ) )

  proof
    wph
    cM
    cpo
    wcel
    #
    cX
    cY
    c.pl
    co
    #
    cB
    wcel
    #
    cX
    cW
    c.pl
    co
    #
    cB
    wcel
    #
    cZ
    cW
    c.pl
    co
    #
    cB
    wcel
    #
    w3a
    #
    @1
    @3
    c.le
    wbr
    #
    @3
    @5
    c.le
    wbr
    #
    @1
    @5
    c.le
    wbr
    #
    wph
    cM
    comnd
    wcel
    #
    cM
    ctos
    wcel
    @0
    omndadd2d.m
    cM
    omndtos
    cM
    tospos
    3syl
    wph
    @2
    @4
    @6
    wph
    cM
    cmnd
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    @2
    wph
    @11
    @12
    omndadd2d.m
    cM
    omndmnd
    syl
    #
    omndadd2d.x
    omndadd2d.y
    cB
    c.pl
    cM
    cX
    cY
    omndadd.0
    omndadd.2
    mndcl
    syl3anc
    wph
    @12
    @13
    cW
    cB
    wcel
    #
    @4
    @15
    omndadd2d.x
    omndadd2d.w
    cB
    c.pl
    cM
    cX
    cW
    omndadd.0
    omndadd.2
    mndcl
    syl3anc
    wph
    @12
    cZ
    cB
    wcel
    #
    @16
    @6
    @15
    omndadd2d.z
    omndadd2d.w
    cB
    c.pl
    cM
    cZ
    cW
    omndadd.0
    omndadd.2
    mndcl
    syl3anc
    3jca
    wph
    cM
    coppg
    cfv
    comnd
    wcel
    @14
    @16
    @13
    cY
    cW
    c.le
    wbr
    @8
    omndadd2rd.c
    omndadd2d.y
    omndadd2d.w
    omndadd2d.x
    omndadd2d.2
    cB
    c.pl
    c.le
    cM
    cY
    cW
    cX
    omndadd.0
    omndadd.1
    omndadd.2
    omndaddr
    syl131anc
    wph
    @11
    @13
    @17
    @16
    cX
    cZ
    c.le
    wbr
    @9
    omndadd2d.m
    omndadd2d.x
    omndadd2d.z
    omndadd2d.w
    omndadd2d.1
    cB
    c.pl
    c.le
    cM
    cX
    cZ
    cW
    omndadd.0
    omndadd.1
    omndadd.2
    omndadd
    syl131anc
    @0
    @7
    wa
    @8
    @9
    wa
    @10
    cB
    cM
    c.le
    @1
    @3
    @5
    omndadd.0
    omndadd.1
    postr
    imp
    syl22anc
end
