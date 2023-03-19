include "cfv.mm"
include "wcel.mm"
include "csn.mm"
include "eldifbd.mm"
include "eldifad.mm"
include "wa.mm"
include "cin.mm"
include "elin.mm"
include "chlt.mm"
include "wceq.mm"
include "dochnoncon.mm"
include "syl2anc.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "biimpd.mm"
include "mpand.mm"
include "mtod.mm"

theorem dochnel2
  let wph: wff ph
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume dochnoncon.h: |- H = ( LHyp ` K )
  assume dochnoncon.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochnoncon.s: |- S = ( LSubSp ` U )
  assume dochnoncon.z: |- .0. = ( 0g ` U )
  assume dochnoncon.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochnel2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochnel2.t: |- ( ph -> T e. S )
  assume dochnel2.x: |- ( ph -> X e. ( T \ { .0. } ) )


  assert |- ( ph -> -. X e. ( ._|_ ` T ) )

  proof
    wph
    cX
    cT
    c.pe
    cfv
    #
    wcel
    #
    cX
    c.0
    csn
    #
    wcel
    #
    wph
    cX
    cT
    @2
    dochnel2.x
    eldifbd
    wph
    cX
    cT
    wcel
    #
    @1
    @3
    wph
    cX
    cT
    @2
    dochnel2.x
    eldifad
    wph
    @4
    @1
    wa
    #
    @3
    @5
    cX
    cT
    @0
    cin
    #
    wcel
    wph
    @3
    cX
    cT
    @0
    elin
    wph
    @6
    @2
    cX
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cT
    cS
    wcel
    @6
    @2
    wceq
    dochnel2.k
    dochnel2.t
    cS
    cU
    cH
    cK
    c.pe
    cW
    cT
    c.0
    dochnoncon.h
    dochnoncon.u
    dochnoncon.s
    dochnoncon.z
    dochnoncon.o
    dochnoncon
    syl2anc
    eleq2d
    syl5bbr
    biimpd
    mpand
    mtod
end
