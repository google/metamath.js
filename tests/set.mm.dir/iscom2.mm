include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "ccm2.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "crn.mm"
include "wral.mm"
include "copab.mm"
include "df-com2.mm"
include "a1i.mm"
include "eleq2d.mm"
include "rneq.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "oveq.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "opelopabg.mm"
include "bitrd.mm"

theorem iscom2
  let cA: class A
  let cB: class B
  let cG: class G
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y

  disjoint G a
  disjoint G b
  disjoint a b
  disjoint H a
  disjoint H b
  disjoint G x
  disjoint G y
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint x y
  disjoint H x
  disjoint H y
  assert |- ( ( G e. A /\ H e. B ) -> ( <. G , H >. e. Com2 <-> A. a e. ran G A. b e. ran G ( a H b ) = ( b H a ) ) )

  proof
    cG
    cA
    wcel
    cH
    cB
    wcel
    wa
    #
    cG
    cH
    cop
    #
    ccm2
    wcel
    @1
    va
    cv
    #
    vb
    cv
    #
    vy
    cv
    #
    co
    #
    @3
    @2
    @4
    co
    #
    wceq
    #
    vb
    vx
    cv
    #
    crn
    #
    wral
    #
    va
    @9
    wral
    #
    vx
    vy
    copab
    #
    wcel
    @2
    @3
    cH
    co
    #
    @3
    @2
    cH
    co
    #
    wceq
    #
    vb
    cG
    crn
    #
    wral
    va
    @16
    wral
    #
    @0
    ccm2
    @12
    @1
    ccm2
    @12
    wceq
    @0
    vx
    vy
    va
    vb
    df-com2
    a1i
    eleq2d
    @11
    @7
    vb
    @16
    wral
    #
    va
    @16
    wral
    @17
    vx
    vy
    cG
    cH
    cA
    cB
    @8
    cG
    wceq
    #
    @10
    @18
    va
    @9
    @16
    @8
    cG
    rneq
    #
    @19
    @7
    vb
    @9
    @16
    @20
    raleqdv
    raleqbidv
    @4
    cH
    wceq
    #
    @7
    @15
    va
    vb
    @16
    @16
    @21
    @5
    @13
    @6
    @14
    @2
    @3
    @4
    cH
    oveq
    @3
    @2
    @4
    cH
    oveq
    eqeq12d
    2ralbidv
    opelopabg
    bitrd
end
