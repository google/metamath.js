include "wwe.mm"
include "cv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cint.mm"
include "cmpt.mm"
include "cfv.mm"
include "cep.mm"
include "wbr.mm"
include "copab.mm"
include "crn.mm"
include "wf1o.mm"
include "con0.mm"
include "wf1.mm"
include "dnnumch3.mm"
include "f1f1orn.mm"
include "syl.mm"
include "wss.mm"
include "wf.mm"
include "f1f.mm"
include "frn.mm"
include "3syl.mm"
include "epweon.mm"
include "wess.mm"
include "mpisyl.mm"
include "eqid.mm"
include "f1owe.mm"
include "sylc.mm"
include "cxp.mm"
include "cin.mm"
include "wceq.mm"
include "wb.mm"
include "wcel.mm"
include "wa.mm"
include "fvex.mm"
include "epelc.mm"
include "dnnumch3lem.mm"
include "adantrr.mm"
include "adantrl.mm"
include "eleq12d.mm"
include "syl5rbb.mm"
include "pm5.32da.mm"
include "opabbidv.mm"
include "incom.mm"
include "df-xp.mm"
include "ineq12i.mm"
include "inopab.mm"
include "3eqtri.mm"
include "ineq1i.mm"
include "3eqtr4g.mm"
include "weeq1.mm"
include "weinxp.mm"
include "3bitr4g.mm"
include "mpbird.mm"

theorem dnwech
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let vx: setvar x
  assume dnnumch.f: |- F = recs ( ( z e. _V |-> ( G ` ( A \ ran z ) ) ) )
  assume dnnumch.a: |- ( ph -> A e. V )
  assume dnnumch.g: |- ( ph -> A. y e. ~P A ( y =/= (/) -> ( G ` y ) e. y ) )
  assume dnwech.h: |- H = { <. v , w >. | |^| ( `' F " { v } ) e. |^| ( `' F " { w } ) }

  disjoint F v
  disjoint F w
  disjoint F y
  disjoint v w
  disjoint v y
  disjoint w y
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint G z
  disjoint v z
  disjoint w z
  disjoint y z
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint ph v
  disjoint ph w
  disjoint F x
  disjoint v x
  disjoint w x
  disjoint x y
  disjoint G x
  disjoint x z
  disjoint A x
  disjoint ph x
  assert |- ( ph -> H We A )

  proof
    wph
    cA
    cH
    wwe
    #
    cA
    vv
    cv
    #
    vx
    cA
    cF
    ccnv
    #
    vx
    cv
    csn
    cima
    cint
    cmpt
    #
    cfv
    #
    vw
    cv
    #
    @3
    cfv
    #
    cep
    wbr
    #
    vv
    vw
    copab
    #
    wwe
    #
    wph
    cA
    @3
    crn
    #
    @3
    wf1o
    #
    @10
    cep
    wwe
    #
    @9
    wph
    cA
    con0
    @3
    wf1
    #
    @11
    wph
    vx
    vy
    vz
    cA
    cF
    cG
    cV
    dnnumch.f
    dnnumch.a
    dnnumch.g
    dnnumch3
    #
    cA
    con0
    @3
    f1f1orn
    syl
    wph
    @10
    con0
    wss
    #
    con0
    cep
    wwe
    @12
    wph
    @13
    cA
    con0
    @3
    wf
    @15
    @14
    cA
    con0
    @3
    f1f
    cA
    con0
    @3
    frn
    3syl
    epweon
    @10
    con0
    cep
    wess
    mpisyl
    vv
    vw
    cA
    @10
    @8
    cep
    @3
    @8
    eqid
    f1owe
    sylc
    wph
    cA
    cH
    cA
    cA
    cxp
    #
    cin
    #
    wwe
    #
    cA
    @8
    @16
    cin
    #
    wwe
    #
    @0
    @9
    wph
    @17
    @19
    wceq
    @18
    @20
    wb
    wph
    @1
    cA
    wcel
    #
    @5
    cA
    wcel
    #
    wa
    #
    @2
    @1
    csn
    cima
    cint
    #
    @2
    @5
    csn
    cima
    cint
    #
    wcel
    #
    wa
    #
    vv
    vw
    copab
    #
    @23
    @7
    wa
    #
    vv
    vw
    copab
    #
    @17
    @19
    wph
    @27
    @29
    vv
    vw
    wph
    @23
    @26
    @7
    @7
    @4
    @6
    wcel
    wph
    @23
    wa
    #
    @26
    @4
    @6
    @5
    @3
    fvex
    epelc
    @31
    @4
    @24
    @6
    @25
    wph
    @21
    @4
    @24
    wceq
    @22
    wph
    vx
    vy
    vz
    vv
    cA
    cF
    cG
    cV
    dnnumch.f
    dnnumch.a
    dnnumch.g
    dnnumch3lem
    adantrr
    wph
    @22
    @6
    @25
    wceq
    @21
    wph
    vx
    vy
    vz
    vw
    cA
    cF
    cG
    cV
    dnnumch.f
    dnnumch.a
    dnnumch.g
    dnnumch3lem
    adantrl
    eleq12d
    syl5rbb
    pm5.32da
    opabbidv
    @17
    @16
    cH
    cin
    @23
    vv
    vw
    copab
    #
    @26
    vv
    vw
    copab
    #
    cin
    @28
    cH
    @16
    incom
    @16
    @32
    cH
    @33
    vv
    vw
    cA
    cA
    df-xp
    #
    dnwech.h
    ineq12i
    @23
    @26
    vv
    vw
    inopab
    3eqtri
    @19
    @16
    @8
    cin
    @32
    @8
    cin
    @30
    @8
    @16
    incom
    @16
    @32
    @8
    @34
    ineq1i
    @23
    @7
    vv
    vw
    inopab
    3eqtri
    3eqtr4g
    cA
    @17
    @19
    weeq1
    syl
    cA
    cH
    weinxp
    cA
    @8
    weinxp
    3bitr4g
    mpbird
end
