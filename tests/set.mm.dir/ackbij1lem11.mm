include "com.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwid.mm"
include "sstr.mm"
include "sylan2.mm"
include "cvv.mm"
include "wb.mm"
include "ssexg.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "ancoms.mm"
include "inss2.mm"
include "ssfi.mm"
include "sylan.mm"
include "elind.mm"

theorem ackbij1lem11
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cG: class G
  let cH: class H
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G x
  disjoint G y
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H x
  disjoint H y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint B a
  disjoint B b
  disjoint B c
  assert |- ( ( A e. ( ~P _om i^i Fin ) /\ B C_ A ) -> B e. ( ~P _om i^i Fin ) )

  proof
    cA
    com
    cpw
    #
    cfn
    cin
    #
    wcel
    #
    cB
    cA
    wss
    #
    wa
    @0
    cfn
    cB
    @3
    @2
    cB
    @0
    wcel
    #
    @3
    @2
    wa
    #
    @4
    cB
    com
    wss
    #
    @2
    @3
    cA
    com
    wss
    @6
    @2
    cA
    com
    @1
    @0
    cA
    @0
    cfn
    inss1
    sseli
    elpwid
    cB
    cA
    com
    sstr
    sylan2
    @5
    cB
    cvv
    wcel
    @4
    @6
    wb
    cB
    cA
    @1
    ssexg
    cB
    com
    cvv
    elpwg
    syl
    mpbird
    ancoms
    @2
    cA
    cfn
    wcel
    @3
    cB
    cfn
    wcel
    @1
    cfn
    cA
    @0
    cfn
    inss2
    sseli
    cA
    cB
    ssfi
    sylan
    elind
end
