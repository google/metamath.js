include "cun.mm"
include "cvv.mm"
include "cdif.mm"
include "cin.mm"
include "cif.mm"
include "inindi.mm"
include "dfif4.mm"
include "undir.mm"
include "unidm.mm"
include "uneq1i.mm"
include "unass.mm"
include "undi.mm"
include "3eqtr3ri.mm"
include "undifabs.mm"
include "ineq1i.mm"
include "inabs.mm"
include "3eqtri.mm"
include "undif2.mm"
include "3eqtr4i.mm"
include "uneq12i.mm"
include "eqtr4i.mm"
include "unundi.mm"
include "uncom.mm"
include "3eqtrri.mm"
include "uneq2i.mm"
include "ineq2i.mm"
include "ineq12i.mm"

theorem dfif5
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
  assert |- if ( ph , A , B ) = ( ( A i^i B ) u. ( ( ( A \ B ) i^i C ) u. ( ( B \ A ) i^i ( _V \ C ) ) ) )

  proof
    cA
    cB
    cun
    #
    cA
    cvv
    cC
    cdif
    #
    cun
    #
    cB
    cC
    cun
    #
    cin
    cin
    @0
    @2
    cin
    #
    @0
    @3
    cin
    #
    cin
    #
    wph
    cA
    cB
    cif
    cA
    cB
    cin
    cA
    cB
    cdif
    #
    cC
    cin
    #
    cB
    cA
    cdif
    #
    @1
    cin
    #
    cun
    #
    cun
    #
    @0
    @2
    @3
    inindi
    wph
    vx
    cA
    cB
    cC
    dfif3.1
    dfif4
    @12
    cA
    @11
    cun
    #
    cB
    @11
    cun
    #
    cin
    @6
    cA
    cB
    @11
    undir
    @4
    @13
    @5
    @14
    @4
    cA
    @8
    cun
    #
    cA
    @10
    cun
    #
    cun
    #
    @13
    @4
    cA
    cA
    cB
    @1
    cin
    #
    cun
    #
    cun
    #
    @17
    cA
    cA
    cun
    #
    @18
    cun
    @19
    @20
    @4
    @21
    cA
    @18
    cA
    unidm
    uneq1i
    cA
    cA
    @18
    unass
    cA
    cB
    @1
    undi
    #
    3eqtr3ri
    @15
    cA
    @16
    @19
    @15
    cA
    @7
    cun
    #
    cA
    cC
    cun
    #
    cin
    cA
    @24
    cin
    cA
    cA
    @7
    cC
    undi
    @23
    cA
    @24
    cA
    cB
    undifabs
    ineq1i
    cA
    cC
    inabs
    3eqtri
    cA
    @9
    cun
    #
    @2
    cin
    @4
    @16
    @19
    @25
    @0
    @2
    cA
    cB
    undif2
    ineq1i
    cA
    @9
    @1
    undi
    @22
    3eqtr4i
    uneq12i
    eqtr4i
    cA
    @8
    @10
    unundi
    eqtr4i
    cA
    cC
    cin
    #
    cB
    cun
    #
    cB
    @8
    cun
    #
    cB
    @10
    cun
    #
    cun
    #
    @5
    @14
    @27
    cB
    cun
    @26
    cB
    cB
    cun
    #
    cun
    @30
    @27
    @26
    cB
    cB
    unass
    @27
    @28
    cB
    @29
    @27
    cB
    @7
    cun
    #
    @3
    cin
    #
    @28
    cB
    @26
    cun
    cB
    cA
    cun
    #
    @3
    cin
    @27
    @33
    cB
    cA
    cC
    undi
    @26
    cB
    uncom
    @32
    @34
    @3
    cB
    cA
    undif2
    ineq1i
    3eqtr4i
    cB
    @7
    cC
    undi
    eqtr4i
    @29
    cB
    @9
    cun
    #
    cB
    @1
    cun
    #
    cin
    cB
    @36
    cin
    cB
    cB
    @9
    @1
    undi
    @35
    cB
    @36
    cB
    cA
    undifabs
    ineq1i
    cB
    @1
    inabs
    3eqtrri
    uneq12i
    @31
    cB
    @26
    cB
    unidm
    uneq2i
    3eqtr3ri
    @5
    @0
    cC
    cB
    cun
    #
    cin
    @27
    @3
    @37
    @0
    cB
    cC
    uncom
    ineq2i
    cA
    cC
    cB
    undir
    eqtr4i
    cB
    @8
    @10
    unundi
    3eqtr4i
    ineq12i
    eqtr4i
    3eqtr4i
end
