include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "cbs.mm"
include "wrex.mm"
include "co.mm"
include "eqid.mm"
include "lcfl8a.mm"
include "mpbid.mm"
include "wcel.mm"
include "wi.mm"
include "w3a.mm"
include "chlt.mm"
include "wa.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "simp23.mm"
include "simp22.mm"
include "simp3.mm"
include "lclkrlem2x.mm"
include "3exp.mm"
include "3expd.mm"
include "rexlimdv.mm"
include "mpd.mm"

theorem lclkrlem2y
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume lclkrlem2y.l: |- L = ( LKer ` U )
  assume lclkrlem2y.h: |- H = ( LHyp ` K )
  assume lclkrlem2y.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lclkrlem2y.u: |- U = ( ( DVecH ` K ) ` W )
  assume lclkrlem2y.f: |- F = ( LFnl ` U )
  assume lclkrlem2y.d: |- D = ( LDual ` U )
  assume lclkrlem2y.p: |- .+ = ( +g ` D )
  assume lclkrlem2y.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lclkrlem2y.e: |- ( ph -> E e. F )
  assume lclkrlem2y.g: |- ( ph -> G e. F )
  assume lclkrlem2y.le: |- ( ph -> ( ._|_ ` ( ._|_ ` ( L ` E ) ) ) = ( L ` E ) )
  assume lclkrlem2y.lg: |- ( ph -> ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) = ( L ` G ) )


  assert |- ( ph -> ( ._|_ ` ( ._|_ ` ( L ` ( E .+ G ) ) ) ) = ( L ` ( E .+ G ) ) )

  proof
    wph
    cG
    cL
    cfv
    #
    vy
    cv
    #
    csn
    c.pe
    cfv
    wceq
    #
    vy
    cU
    cbs
    cfv
    #
    wrex
    #
    cE
    cG
    c.pl
    co
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @5
    wceq
    #
    wph
    @0
    c.pe
    cfv
    c.pe
    cfv
    @0
    wceq
    @4
    lclkrlem2y.lg
    wph
    vy
    cU
    cF
    cG
    cH
    cK
    cL
    c.pe
    @3
    cW
    lclkrlem2y.h
    lclkrlem2y.o
    lclkrlem2y.u
    @3
    eqid
    #
    lclkrlem2y.f
    lclkrlem2y.l
    lclkrlem2y.k
    lclkrlem2y.g
    lcfl8a
    mpbid
    wph
    @2
    @6
    vy
    @3
    wph
    cE
    cL
    cfv
    #
    vx
    cv
    #
    csn
    c.pe
    cfv
    wceq
    #
    vx
    @3
    wrex
    #
    @1
    @3
    wcel
    #
    @2
    @6
    wi
    #
    wi
    #
    wph
    @8
    c.pe
    cfv
    c.pe
    cfv
    @8
    wceq
    @11
    lclkrlem2y.le
    wph
    vx
    cU
    cF
    cE
    cH
    cK
    cL
    c.pe
    @3
    cW
    lclkrlem2y.h
    lclkrlem2y.o
    lclkrlem2y.u
    @7
    lclkrlem2y.f
    lclkrlem2y.l
    lclkrlem2y.k
    lclkrlem2y.e
    lcfl8a
    mpbid
    wph
    @10
    @14
    vx
    @3
    wph
    @9
    @3
    wcel
    #
    @10
    @12
    @13
    wph
    @15
    @10
    @12
    w3a
    #
    @2
    @6
    wph
    @16
    @2
    w3a
    cD
    c.pl
    cU
    cE
    cF
    cG
    cH
    cK
    cL
    c.pe
    @3
    cW
    @9
    @1
    lclkrlem2y.l
    lclkrlem2y.h
    lclkrlem2y.o
    lclkrlem2y.u
    @7
    lclkrlem2y.f
    lclkrlem2y.d
    lclkrlem2y.p
    wph
    @16
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @2
    lclkrlem2y.k
    3ad2ant1
    wph
    @15
    @10
    @12
    @2
    simp21
    wph
    @15
    @10
    @12
    @2
    simp23
    wph
    @16
    cE
    cF
    wcel
    @2
    lclkrlem2y.e
    3ad2ant1
    wph
    @16
    cG
    cF
    wcel
    @2
    lclkrlem2y.g
    3ad2ant1
    wph
    @15
    @10
    @12
    @2
    simp22
    wph
    @16
    @2
    simp3
    lclkrlem2x
    3exp
    3expd
    rexlimdv
    mpd
    rexlimdv
    mpd
end
