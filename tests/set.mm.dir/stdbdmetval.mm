include "wcel.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "wceq.mm"
include "cvv.mm"
include "ovex.mm"
include "ifexg.mm"
include "mpan.mm"
include "cv.mm"
include "wa.mm"
include "oveq12.mm"
include "breq1d.mm"
include "ifbieq1d.mm"
include "ovmpt2ga.mm"
include "syl3an3.mm"
include "3comr.mm"

theorem stdbdmetval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  let vz: setvar z
  let cJ: class J
  let cS: class S
  let cP: class P
  assume stdbdmet.1: |- D = ( x e. X , y e. X |-> if ( ( x C y ) <_ R , ( x C y ) , R ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint C x
  disjoint C y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint a b
  disjoint a r
  disjoint a s
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint b r
  disjoint b s
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint C b
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint C r
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint C s
  disjoint x z
  disjoint y z
  disjoint C z
  disjoint D r
  disjoint D s
  disjoint D z
  disjoint J r
  disjoint J s
  disjoint J z
  disjoint S z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint R a
  disjoint R b
  disjoint R r
  disjoint R s
  disjoint R z
  disjoint X a
  disjoint X b
  disjoint X r
  disjoint X s
  disjoint X z
  assert |- ( ( R e. V /\ A e. X /\ B e. X ) -> ( A D B ) = if ( ( A C B ) <_ R , ( A C B ) , R ) )

  proof
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cR
    cV
    wcel
    #
    cA
    cB
    cD
    co
    cA
    cB
    cC
    co
    #
    cR
    cle
    wbr
    #
    @3
    cR
    cif
    #
    wceq
    #
    @2
    @0
    @1
    @5
    cvv
    wcel
    #
    @6
    @3
    cvv
    wcel
    @2
    @7
    cA
    cB
    cC
    ovex
    @4
    @3
    cR
    cvv
    cV
    ifexg
    mpan
    vx
    vy
    cA
    cB
    cX
    cX
    vx
    cv
    #
    vy
    cv
    #
    cC
    co
    #
    cR
    cle
    wbr
    #
    @10
    cR
    cif
    @5
    cD
    cvv
    @8
    cA
    wceq
    @9
    cB
    wceq
    wa
    #
    @11
    @4
    @10
    @3
    cR
    @12
    @10
    @3
    cR
    cle
    @8
    cA
    @9
    cB
    cC
    oveq12
    #
    breq1d
    @13
    ifbieq1d
    stdbdmet.1
    ovmpt2ga
    syl3an3
    3comr
end
