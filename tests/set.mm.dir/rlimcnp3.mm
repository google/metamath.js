include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "crp.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "wcel.mm"
include "0e0icopnf.mm"
include "cr.mm"
include "rpssre.mm"
include "cv.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "simpr.mm"
include "cle.mm"
include "wbr.mm"
include "rpreccl.mm"
include "adantl.mm"
include "rpred.mm"
include "rpge0d.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "2thd.mm"
include "rlimcnp2.mm"

theorem rlimcnp3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cR: class R
  let cS: class S
  let cJ: class J
  let cK: class K
  assume rlimcnp3.c: |- ( ph -> C e. CC )
  assume rlimcnp3.r: |- ( ( ph /\ y e. RR+ ) -> S e. CC )
  assume rlimcnp3.s: |- ( y = ( 1 / x ) -> S = R )
  assume rlimcnp3.j: |- J = ( TopOpen ` CCfld )
  assume rlimcnp3.k: |- K = ( J |`t ( 0 [,) +oo ) )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint ph x
  disjoint ph y
  disjoint R y
  disjoint S x
  assert |- ( ph -> ( ( y e. RR+ |-> S ) ~~>r C <-> ( x e. ( 0 [,) +oo ) |-> if ( x = 0 , C , R ) ) e. ( ( K CnP J ) ` 0 ) ) )

  proof
    wph
    vx
    vy
    cc0
    cpnf
    cico
    co
    #
    crp
    cC
    cR
    cS
    cJ
    cK
    @0
    @0
    wss
    wph
    @0
    ssid
    a1i
    cc0
    @0
    wcel
    wph
    0e0icopnf
    a1i
    crp
    cr
    wss
    wph
    rpssre
    a1i
    rlimcnp3.c
    rlimcnp3.r
    wph
    vy
    cv
    #
    crp
    wcel
    #
    wa
    #
    @2
    c1
    @1
    cdiv
    co
    #
    @0
    wcel
    #
    wph
    @2
    simpr
    @3
    @4
    cr
    wcel
    cc0
    @4
    cle
    wbr
    @5
    @3
    @4
    @2
    @4
    crp
    wcel
    wph
    @1
    rpreccl
    adantl
    #
    rpred
    @3
    @4
    @6
    rpge0d
    @4
    elrege0
    sylanbrc
    2thd
    rlimcnp3.s
    rlimcnp3.j
    rlimcnp3.k
    rlimcnp2
end
