include "cdr.mm"
include "wcel.mm"
include "cmulr.mm"
include "cfv.mm"
include "eqid.mm"
include "drngring.mm"
include "cv.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "biid.mm"
include "eldifsn.mm"
include "drngmcl.mm"
include "syl3anbr.mm"
include "sylib.mm"
include "simprd.mm"
include "abvtrivd.mm"

theorem abvtriv
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph
  let c.x: class .x.
  assume abvtriv.a: |- A = ( AbsVal ` R )
  assume abvtriv.b: |- B = ( Base ` R )
  assume abvtriv.z: |- .0. = ( 0g ` R )
  assume abvtriv.f: |- F = ( x e. B |-> if ( x = .0. , 0 , 1 ) )

  disjoint .0. x
  disjoint R x
  disjoint B x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint R y
  disjoint R z
  disjoint .x. x
  assert |- ( R e. DivRing -> F e. A )

  proof
    cR
    cdr
    wcel
    #
    vx
    vy
    vz
    cA
    cB
    cR
    cR
    cmulr
    cfv
    #
    cF
    c.0
    abvtriv.a
    abvtriv.b
    abvtriv.z
    abvtriv.f
    @1
    eqid
    #
    cR
    drngring
    @0
    vy
    cv
    #
    cB
    wcel
    @3
    c.0
    wne
    wa
    #
    vz
    cv
    #
    cB
    wcel
    @5
    c.0
    wne
    wa
    #
    w3a
    #
    @3
    @5
    @1
    co
    #
    cB
    wcel
    #
    @8
    c.0
    wne
    #
    @7
    @8
    cB
    c.0
    csn
    cdif
    #
    wcel
    #
    @9
    @10
    wa
    @0
    @0
    @4
    @3
    @11
    wcel
    @6
    @5
    @11
    wcel
    @12
    @0
    biid
    @3
    cB
    c.0
    eldifsn
    @5
    cB
    c.0
    eldifsn
    cB
    cR
    @1
    @3
    @5
    c.0
    abvtriv.b
    @2
    abvtriv.z
    drngmcl
    syl3anbr
    @8
    cB
    c.0
    eldifsn
    sylib
    simprd
    abvtrivd
end
