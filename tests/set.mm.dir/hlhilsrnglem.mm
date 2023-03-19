include "hlhilsbase2.mm"
include "hlhilsplus2.mm"
include "hlhilsmul2.mm"
include "hlhilnvl.mm"
include "cdr.mm"
include "wcel.mm"
include "crg.mm"
include "hlhildrng.mm"
include "drngring.mm"
include "syl.mm"
include "cv.mm"
include "wa.mm"
include "chlt.mm"
include "adantr.mm"
include "simpr.mm"
include "hgmapcl.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "hgmapadd.mm"
include "hgmapmul.mm"
include "hgmapvv.mm"
include "issrngd.mm"

theorem hlhilsrnglem
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume hlhillvec.h: |- H = ( LHyp ` K )
  assume hlhillvec.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhillvec.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhildrng.r: |- R = ( Scalar ` U )
  assume hlhilsrng.l: |- L = ( ( DVecH ` K ) ` W )
  assume hlhilsrng.s: |- S = ( Scalar ` L )
  assume hlhilsrng.b: |- B = ( Base ` S )
  assume hlhilsrng.p: |- .+ = ( +g ` S )
  assume hlhilsrng.t: |- .x. = ( .r ` S )
  assume hlhilsrng.g: |- G = ( ( HGMap ` K ) ` W )


  assert |- ( ph -> R e. *Ring )

  proof
    wph
    vx
    vy
    c.pl
    cR
    c.x
    cG
    cB
    wph
    cB
    cR
    cS
    cU
    cH
    cK
    cL
    cW
    hlhillvec.h
    hlhilsrng.l
    hlhilsrng.s
    hlhillvec.u
    hlhildrng.r
    hlhillvec.k
    hlhilsrng.b
    hlhilsbase2
    wph
    c.pl
    cR
    cS
    cU
    cH
    cK
    cL
    cW
    hlhillvec.h
    hlhilsrng.l
    hlhilsrng.s
    hlhillvec.u
    hlhildrng.r
    hlhillvec.k
    hlhilsrng.p
    hlhilsplus2
    wph
    cR
    cS
    c.x
    cU
    cH
    cK
    cL
    cW
    hlhillvec.h
    hlhilsrng.l
    hlhilsrng.s
    hlhillvec.u
    hlhildrng.r
    hlhillvec.k
    hlhilsrng.t
    hlhilsmul2
    wph
    cR
    cU
    cH
    cG
    cK
    cW
    hlhillvec.h
    hlhillvec.u
    hlhildrng.r
    hlhilsrng.g
    hlhillvec.k
    hlhilnvl
    wph
    cR
    cdr
    wcel
    cR
    crg
    wcel
    wph
    cR
    cU
    cH
    cK
    cW
    hlhillvec.h
    hlhillvec.u
    hlhillvec.k
    hlhildrng.r
    hlhildrng
    cR
    drngring
    syl
    wph
    vx
    cv
    #
    cB
    wcel
    #
    wa
    #
    cB
    cS
    cL
    @0
    cG
    cH
    cK
    cW
    hlhillvec.h
    hlhilsrng.l
    hlhilsrng.s
    hlhilsrng.b
    hlhilsrng.g
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @1
    hlhillvec.k
    adantr
    #
    wph
    @1
    simpr
    #
    hgmapcl
    wph
    @1
    vy
    cv
    #
    cB
    wcel
    #
    w3a
    #
    cB
    c.pl
    cS
    cL
    cG
    cH
    cK
    cW
    @0
    @6
    hlhillvec.h
    hlhilsrng.l
    hlhilsrng.s
    hlhilsrng.b
    hlhilsrng.p
    hlhilsrng.g
    wph
    @1
    @3
    @7
    hlhillvec.k
    3ad2ant1
    #
    wph
    @1
    @7
    simp2
    #
    wph
    @1
    @7
    simp3
    #
    hgmapadd
    @8
    cB
    cS
    c.x
    cL
    cG
    cH
    cK
    cW
    @0
    @6
    hlhillvec.h
    hlhilsrng.l
    hlhilsrng.s
    hlhilsrng.b
    hlhilsrng.t
    hlhilsrng.g
    @9
    @10
    @11
    hgmapmul
    @2
    cB
    cS
    cL
    cG
    cH
    cK
    cW
    @0
    hlhillvec.h
    hlhilsrng.l
    hlhilsrng.s
    hlhilsrng.b
    hlhilsrng.g
    @4
    @5
    hgmapvv
    issrngd
end
