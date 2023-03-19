include "wfn.mm"
include "wa.mm"
include "c1st.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "ccnv.mm"
include "ccom.mm"
include "c2nd.mm"
include "cin.mm"
include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "ciun.mm"
include "cop.mm"
include "cmpt2.mm"
include "fparlem3.mm"
include "fparlem4.mm"
include "ineqan12d.mm"
include "opex.mm"
include "dfmpt2.mm"
include "wceq.mm"
include "wcel.mm"
include "inxp.mm"
include "inv1.mm"
include "incom.mm"
include "eqtri.mm"
include "xpeq12i.mm"
include "vex.mm"
include "xpsn.mm"
include "3eqtri.mm"
include "fvex.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "2iunin.mm"
include "3eqtr2i.mm"
include "3eqtr4g.mm"

theorem fpar
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  assume fpar.1: |- H = ( ( `' ( 1st |` ( _V X. _V ) ) o. ( F o. ( 1st |` ( _V X. _V ) ) ) ) i^i ( `' ( 2nd |` ( _V X. _V ) ) o. ( G o. ( 2nd |` ( _V X. _V ) ) ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  assert |- ( ( F Fn A /\ G Fn B ) -> H = ( x e. A , y e. B |-> <. ( F ` x ) , ( G ` y ) >. ) )

  proof
    cF
    cA
    wfn
    #
    cG
    cB
    wfn
    #
    wa
    c1st
    cvv
    cvv
    cxp
    #
    cres
    #
    ccnv
    cF
    @3
    ccom
    ccom
    #
    c2nd
    @2
    cres
    #
    ccnv
    cG
    @5
    ccom
    ccom
    #
    cin
    vx
    cA
    vx
    cv
    #
    csn
    #
    cvv
    cxp
    #
    @7
    cF
    cfv
    #
    csn
    #
    cvv
    cxp
    #
    cxp
    #
    ciun
    #
    vy
    cB
    cvv
    vy
    cv
    #
    csn
    #
    cxp
    #
    cvv
    @15
    cG
    cfv
    #
    csn
    #
    cxp
    #
    cxp
    #
    ciun
    #
    cin
    #
    cH
    vx
    vy
    cA
    cB
    @10
    @18
    cop
    #
    cmpt2
    #
    @0
    @1
    @4
    @14
    @6
    @22
    vx
    cA
    cF
    fparlem3
    vy
    cB
    cG
    fparlem4
    ineqan12d
    fpar.1
    @25
    vx
    cA
    vy
    cB
    @7
    @15
    cop
    #
    @24
    cop
    csn
    #
    ciun
    #
    ciun
    vx
    cA
    vy
    cB
    @13
    @21
    cin
    #
    ciun
    #
    ciun
    @23
    vx
    vy
    cA
    cB
    @24
    @10
    @18
    opex
    #
    dfmpt2
    vx
    cA
    @30
    @28
    @30
    @28
    wceq
    @7
    cA
    wcel
    vy
    cB
    @29
    @27
    @29
    @27
    wceq
    @15
    cB
    wcel
    @29
    @9
    @17
    cin
    #
    @12
    @20
    cin
    #
    cxp
    @26
    csn
    #
    @24
    csn
    #
    cxp
    @27
    @9
    @12
    @17
    @20
    inxp
    @32
    @34
    @33
    @35
    @32
    @8
    cvv
    cin
    #
    cvv
    @16
    cin
    #
    cxp
    @8
    @16
    cxp
    @34
    @8
    cvv
    cvv
    @16
    inxp
    @36
    @8
    @37
    @16
    @8
    inv1
    @37
    @16
    cvv
    cin
    @16
    cvv
    @16
    incom
    @16
    inv1
    eqtri
    xpeq12i
    @7
    @15
    vx
    vex
    vy
    vex
    xpsn
    3eqtri
    @33
    @11
    cvv
    cin
    #
    cvv
    @19
    cin
    #
    cxp
    @11
    @19
    cxp
    @35
    @11
    cvv
    cvv
    @19
    inxp
    @38
    @11
    @39
    @19
    @11
    inv1
    @39
    @19
    cvv
    cin
    @19
    cvv
    @19
    incom
    @19
    inv1
    eqtri
    xpeq12i
    @10
    @18
    @7
    cF
    fvex
    @15
    cG
    fvex
    xpsn
    3eqtri
    xpeq12i
    @26
    @24
    @7
    @15
    opex
    @31
    xpsn
    3eqtri
    a1i
    iuneq2i
    a1i
    iuneq2i
    vx
    vy
    cA
    cB
    @13
    @21
    2iunin
    3eqtr2i
    3eqtr4g
end
