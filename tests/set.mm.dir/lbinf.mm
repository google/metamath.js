include "cr.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "crio.mm"
include "clt.mm"
include "wor.mm"
include "ltso.mm"
include "a1i.mm"
include "wcel.mm"
include "lbcl.mm"
include "wi.mm"
include "ssel.mm"
include "adantr.mm"
include "mpd.mm"
include "ssel2.mm"
include "adantlr.mm"
include "lble.mm"
include "3expa.mm"
include "lensymd.mm"
include "infmin.mm"

theorem lbinf
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let vz: setvar z

  disjoint S x
  disjoint S y
  disjoint x y
  disjoint S z
  disjoint x z
  disjoint y z
  assert |- ( ( S C_ RR /\ E. x e. S A. y e. S x <_ y ) -> inf ( S , RR , < ) = ( iota_ x e. S A. y e. S x <_ y ) )

  proof
    cS
    cr
    wss
    #
    vx
    cv
    vy
    cv
    cle
    wbr
    vy
    cS
    wral
    #
    vx
    cS
    wrex
    #
    wa
    #
    vz
    cr
    cS
    @1
    vx
    cS
    crio
    #
    clt
    cr
    clt
    wor
    @3
    ltso
    a1i
    @3
    @4
    cS
    wcel
    #
    @4
    cr
    wcel
    #
    vx
    vy
    cS
    lbcl
    #
    @0
    @5
    @6
    wi
    @2
    cS
    cr
    @4
    ssel
    adantr
    mpd
    #
    @7
    @3
    vz
    cv
    #
    cS
    wcel
    #
    wa
    @4
    @9
    @3
    @6
    @10
    @8
    adantr
    @0
    @10
    @9
    cr
    wcel
    @2
    cS
    cr
    @9
    ssel2
    adantlr
    @0
    @2
    @10
    @4
    @9
    cle
    wbr
    vx
    vy
    @9
    cS
    lble
    3expa
    lensymd
    infmin
end
