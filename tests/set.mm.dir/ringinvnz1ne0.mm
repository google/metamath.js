include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "wcel.mm"
include "wa.mm"
include "oveq2.mm"
include "wi.mm"
include "crg.mm"
include "ringrz.mm"
include "sylan.mm"
include "eqeq12.mm"
include "biimpd.mm"
include "ex.mm"
include "mpan9.mm"
include "syl5.mm"
include "ringridm.mm"
include "eqeq12d.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "impbid.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "necon3bid.mm"

theorem ringinvnz1ne0
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  assume ringinvnzdiv.b: |- B = ( Base ` R )
  assume ringinvnzdiv.t: |- .x. = ( .r ` R )
  assume ringinvnzdiv.u: |- .1. = ( 1r ` R )
  assume ringinvnzdiv.z: |- .0. = ( 0g ` R )
  assume ringinvnzdiv.r: |- ( ph -> R e. Ring )
  assume ringinvnzdiv.x: |- ( ph -> X e. B )
  assume ringinvnzdiv.a: |- ( ph -> E. a e. B ( a .x. X ) = .1. )

  disjoint X a
  disjoint .0. a
  disjoint .1. a
  disjoint .x. a
  disjoint a ph
  assert |- ( ph -> ( X =/= .0. <-> .1. =/= .0. ) )

  proof
    wph
    cX
    c.0
    c.1
    c.0
    wph
    va
    cv
    #
    cX
    c.x
    co
    #
    c.1
    wceq
    #
    va
    cB
    wrex
    cX
    c.0
    wceq
    #
    c.1
    c.0
    wceq
    #
    wb
    #
    ringinvnzdiv.a
    wph
    @2
    @5
    va
    cB
    wph
    @0
    cB
    wcel
    #
    wa
    #
    @2
    @5
    @7
    @2
    wa
    #
    @3
    @4
    @3
    @1
    @0
    c.0
    c.x
    co
    #
    wceq
    #
    @8
    @4
    cX
    c.0
    @0
    c.x
    oveq2
    @7
    @9
    c.0
    wceq
    #
    @2
    @10
    @4
    wi
    #
    wph
    cR
    crg
    wcel
    #
    @6
    @11
    ringinvnzdiv.r
    cB
    cR
    c.x
    @0
    c.0
    ringinvnzdiv.b
    ringinvnzdiv.t
    ringinvnzdiv.z
    ringrz
    sylan
    @2
    @11
    @12
    @2
    @11
    wa
    @10
    @4
    @1
    c.1
    @9
    c.0
    eqeq12
    biimpd
    ex
    mpan9
    syl5
    @4
    cX
    c.1
    c.x
    co
    #
    cX
    c.0
    c.x
    co
    #
    wceq
    #
    @8
    @3
    c.1
    c.0
    cX
    c.x
    oveq2
    wph
    @16
    @3
    wi
    #
    @6
    @2
    wph
    @13
    cX
    cB
    wcel
    #
    @17
    ringinvnzdiv.r
    ringinvnzdiv.x
    @13
    @18
    wa
    #
    @16
    @3
    @19
    @14
    cX
    @15
    c.0
    cB
    cR
    c.x
    c.1
    cX
    ringinvnzdiv.b
    ringinvnzdiv.t
    ringinvnzdiv.u
    ringridm
    cB
    cR
    c.x
    cX
    c.0
    ringinvnzdiv.b
    ringinvnzdiv.t
    ringinvnzdiv.z
    ringrz
    eqeq12d
    biimpd
    syl2anc
    ad2antrr
    syl5
    impbid
    ex
    rexlimdva
    mpd
    necon3bid
end
