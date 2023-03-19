include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cple.mm"
include "cpr.mm"
include "cvv.mm"
include "prex.mm"
include "eqeltri.mm"
include "wcel.mm"
include "wceq.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "df-ple.mm"
include "1lt10.mm"
include "10nn.mm"
include "2strbas.mm"
include "ax-mp.mm"
include "2strop.mm"
include "isposi.mm"

theorem isposix
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cK: class K
  let c.le: class .<_
  assume isposix.a: |- B e. _V
  assume isposix.b: |- .<_ e. _V
  assume isposix.k: |- K = { <. ( Base ` ndx ) , B >. , <. ( le ` ndx ) , .<_ >. }
  assume isposix.1: |- ( x e. B -> x .<_ x )
  assume isposix.2: |- ( ( x e. B /\ y e. B ) -> ( ( x .<_ y /\ y .<_ x ) -> x = y ) )
  assume isposix.3: |- ( ( x e. B /\ y e. B /\ z e. B ) -> ( ( x .<_ y /\ y .<_ z ) -> x .<_ z ) )

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ z
  assert |- K e. Poset

  proof
    vx
    vy
    vz
    cB
    cK
    c.le
    cK
    cnx
    cbs
    cfv
    cB
    cop
    #
    cnx
    cple
    cfv
    c.le
    cop
    #
    cpr
    cvv
    isposix.k
    @0
    @1
    prex
    eqeltri
    cB
    cvv
    wcel
    cB
    cK
    cbs
    cfv
    wceq
    isposix.a
    cB
    c.le
    cple
    cK
    c1
    cc0
    cdc
    #
    cvv
    isposix.k
    df-ple
    1lt10
    10nn
    2strbas
    ax-mp
    c.le
    cvv
    wcel
    c.le
    cK
    cple
    cfv
    wceq
    isposix.b
    cB
    c.le
    cple
    cK
    @2
    cvv
    isposix.k
    df-ple
    1lt10
    10nn
    2strop
    ax-mp
    isposix.1
    isposix.2
    isposix.3
    isposi
end
