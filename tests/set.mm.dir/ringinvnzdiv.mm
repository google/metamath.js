include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "wi.mm"
include "wcel.mm"
include "wa.mm"
include "crg.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "ad3antrrr.mm"
include "oveq1.mm"
include "eqcoms.mm"
include "adantl.mm"
include "w3a.mm"
include "adantr.mm"
include "simpr.mm"
include "3jca.mm"
include "jca.mm"
include "ringass.mm"
include "syl.mm"
include "eqtrd.mm"
include "oveq2.mm"
include "ringrz.mm"
include "sylan.mm"
include "sylan9eqr.mm"
include "3eqtrd.mm"
include "exp31.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ex.mm"
include "impbid.mm"

theorem ringinvnzdiv
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let va: setvar a
  assume ringinvnzdiv.b: |- B = ( Base ` R )
  assume ringinvnzdiv.t: |- .x. = ( .r ` R )
  assume ringinvnzdiv.u: |- .1. = ( 1r ` R )
  assume ringinvnzdiv.z: |- .0. = ( 0g ` R )
  assume ringinvnzdiv.r: |- ( ph -> R e. Ring )
  assume ringinvnzdiv.x: |- ( ph -> X e. B )
  assume ringinvnzdiv.a: |- ( ph -> E. a e. B ( a .x. X ) = .1. )
  assume ringinvnzdiv.y: |- ( ph -> Y e. B )

  disjoint X a
  disjoint .0. a
  disjoint .1. a
  disjoint .x. a
  disjoint a ph
  disjoint Y a
  assert |- ( ph -> ( ( X .x. Y ) = .0. <-> Y = .0. ) )

  proof
    wph
    cX
    cY
    c.x
    co
    #
    c.0
    wceq
    #
    cY
    c.0
    wceq
    #
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
    @1
    @2
    wi
    #
    ringinvnzdiv.a
    wph
    @5
    @6
    va
    cB
    wph
    @3
    cB
    wcel
    #
    wa
    #
    @5
    @1
    @2
    @8
    @5
    wa
    #
    @1
    wa
    cY
    c.1
    cY
    c.x
    co
    #
    @3
    @0
    c.x
    co
    #
    c.0
    wph
    cY
    @10
    wceq
    @7
    @5
    @1
    wph
    @10
    cY
    wph
    cR
    crg
    wcel
    #
    cY
    cB
    wcel
    #
    @10
    cY
    wceq
    ringinvnzdiv.r
    ringinvnzdiv.y
    cB
    cR
    c.x
    c.1
    cY
    ringinvnzdiv.b
    ringinvnzdiv.t
    ringinvnzdiv.u
    ringlidm
    syl2anc
    eqcomd
    ad3antrrr
    @9
    @10
    @11
    wceq
    @1
    @9
    @10
    @4
    cY
    c.x
    co
    #
    @11
    @5
    @10
    @14
    wceq
    #
    @8
    @15
    c.1
    @4
    c.1
    @4
    cY
    c.x
    oveq1
    eqcoms
    adantl
    @9
    @12
    @7
    cX
    cB
    wcel
    #
    @13
    w3a
    #
    wa
    #
    @14
    @11
    wceq
    @8
    @18
    @5
    @8
    @12
    @17
    wph
    @12
    @7
    ringinvnzdiv.r
    adantr
    @8
    @7
    @16
    @13
    wph
    @7
    simpr
    wph
    @16
    @7
    ringinvnzdiv.x
    adantr
    wph
    @13
    @7
    ringinvnzdiv.y
    adantr
    3jca
    jca
    adantr
    cB
    cR
    c.x
    @3
    cX
    cY
    ringinvnzdiv.b
    ringinvnzdiv.t
    ringass
    syl
    eqtrd
    adantr
    @1
    @9
    @11
    @3
    c.0
    c.x
    co
    #
    c.0
    @0
    c.0
    @3
    c.x
    oveq2
    @8
    @19
    c.0
    wceq
    #
    @5
    wph
    @12
    @7
    @20
    ringinvnzdiv.r
    cB
    cR
    c.x
    @3
    c.0
    ringinvnzdiv.b
    ringinvnzdiv.t
    ringinvnzdiv.z
    ringrz
    sylan
    adantr
    sylan9eqr
    3eqtrd
    exp31
    rexlimdva
    mpd
    wph
    @2
    @1
    @2
    wph
    @0
    cX
    c.0
    c.x
    co
    #
    c.0
    cY
    c.0
    cX
    c.x
    oveq2
    wph
    @12
    @16
    @21
    c.0
    wceq
    ringinvnzdiv.r
    ringinvnzdiv.x
    cB
    cR
    c.x
    cX
    c.0
    ringinvnzdiv.b
    ringinvnzdiv.t
    ringinvnzdiv.z
    ringrz
    syl2anc
    sylan9eqr
    ex
    impbid
end
