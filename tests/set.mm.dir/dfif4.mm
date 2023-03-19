include "cif.mm"
include "cin.mm"
include "cvv.mm"
include "cdif.mm"
include "cun.mm"
include "dfif3.mm"
include "undir.mm"
include "undi.mm"
include "uncom.mm"
include "unvdif.mm"
include "ineq12i.mm"
include "inv1.mm"
include "3eqtri.mm"
include "inass.mm"
include "eqtri.mm"

theorem dfif4
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume dfif3.1: |- C = { x | ph }

  disjoint ph x
  disjoint A y
  disjoint B y
  disjoint x y
  disjoint ph y
  assert |- if ( ph , A , B ) = ( ( A u. B ) i^i ( ( A u. ( _V \ C ) ) i^i ( B u. C ) ) )

  proof
    wph
    cA
    cB
    cif
    cA
    cC
    cin
    cB
    cvv
    cC
    cdif
    #
    cin
    #
    cun
    cA
    @1
    cun
    #
    cC
    @1
    cun
    #
    cin
    #
    cA
    cB
    cun
    #
    cA
    @0
    cun
    #
    cB
    cC
    cun
    #
    cin
    cin
    #
    wph
    vx
    cA
    cB
    cC
    dfif3.1
    dfif3
    cA
    cC
    @1
    undir
    @4
    @5
    @6
    cin
    #
    @7
    cin
    @8
    @2
    @9
    @3
    @7
    cA
    cB
    @0
    undi
    @3
    cC
    cB
    cun
    #
    cC
    @0
    cun
    #
    cin
    @7
    cvv
    cin
    @7
    cC
    cB
    @0
    undi
    @10
    @7
    @11
    cvv
    cC
    cB
    uncom
    cC
    unvdif
    ineq12i
    @7
    inv1
    3eqtri
    ineq12i
    @5
    @6
    @7
    inass
    eqtri
    3eqtri
end
