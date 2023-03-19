include "cperpg.mm"
include "cfv.mm"
include "wbr.mm"
include "cop.mm"
include "cv.mm"
include "crn.mm"
include "wcel.mm"
include "wa.mm"
include "cs3.mm"
include "crag.mm"
include "wral.mm"
include "cin.mm"
include "wrex.mm"
include "copab.mm"
include "df-br.mm"
include "clng.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-perpg.mm"
include "a1i.mm"
include "simpr.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "rexralbidv.mm"
include "opabbidv.mm"
include "cstrkg.mm"
include "elex.mm"
include "syl.mm"
include "cxp.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rnexg.mm"
include "mp1i.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "wss.mm"
include "opabssxp.mm"
include "ssexd.mm"
include "fvmptd.mm"
include "syl5bb.mm"
include "wb.mm"
include "ineq12.mm"
include "simpll.mm"
include "simpllr.mm"
include "raleqdv.mm"
include "raleqbidva.mm"
include "rexeqbidva.mm"
include "opelopab2a.mm"
include "bitrd.mm"

theorem isperp
  let wph: wff ph
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  assume isperp.p: |- P = ( Base ` G )
  assume isperp.d: |- .- = ( dist ` G )
  assume isperp.i: |- I = ( Itv ` G )
  assume isperp.l: |- L = ( LineG ` G )
  assume isperp.g: |- ( ph -> G e. TarskiG )
  assume isperp.a: |- ( ph -> A e. ran L )
  assume isperp.b: |- ( ph -> B e. ran L )

  disjoint u v
  disjoint u x
  disjoint A u
  disjoint v x
  disjoint A v
  disjoint A x
  disjoint B u
  disjoint B v
  disjoint B x
  disjoint G u
  disjoint G v
  disjoint G x
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint a b
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint A a
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint a g
  disjoint G a
  disjoint b g
  disjoint G b
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint G g
  disjoint L a
  disjoint L b
  disjoint L g
  disjoint a ph
  disjoint b ph
  disjoint g ph
  assert |- ( ph -> ( A ( perpG ` G ) B <-> E. x e. ( A i^i B ) A. u e. A A. v e. B <" u x v "> e. ( raG ` G ) ) )

  proof
    wph
    cA
    cB
    cG
    cperpg
    cfv
    #
    wbr
    #
    cA
    cB
    cop
    #
    va
    cv
    #
    cL
    crn
    #
    wcel
    #
    vb
    cv
    #
    @4
    wcel
    #
    wa
    #
    vu
    cv
    #
    vx
    cv
    #
    vv
    cv
    cs3
    #
    cG
    crag
    cfv
    #
    wcel
    #
    vv
    @6
    wral
    #
    vu
    @3
    wral
    #
    vx
    @3
    @6
    cin
    #
    wrex
    #
    wa
    #
    va
    vb
    copab
    #
    wcel
    #
    @13
    vv
    cB
    wral
    #
    vu
    cA
    wral
    #
    vx
    cA
    cB
    cin
    #
    wrex
    #
    @1
    @2
    @0
    wcel
    wph
    @20
    cA
    cB
    @0
    df-br
    wph
    @0
    @19
    @2
    wph
    vg
    cG
    @3
    vg
    cv
    #
    clng
    cfv
    #
    crn
    #
    wcel
    #
    @6
    @27
    wcel
    #
    wa
    #
    @11
    @25
    crag
    cfv
    #
    wcel
    #
    vv
    @6
    wral
    #
    vu
    @3
    wral
    vx
    @16
    wrex
    #
    wa
    #
    va
    vb
    copab
    #
    @19
    cvv
    cperpg
    cvv
    cperpg
    vg
    cvv
    @36
    cmpt
    wceq
    wph
    vx
    vv
    vu
    vg
    va
    vb
    df-perpg
    a1i
    wph
    @25
    cG
    wceq
    #
    wa
    #
    @35
    @18
    va
    vb
    @38
    @30
    @8
    @34
    @17
    @38
    @28
    @5
    @29
    @7
    @38
    @27
    @4
    @3
    @38
    @26
    cL
    @38
    @26
    cG
    clng
    cfv
    #
    cL
    @38
    @25
    cG
    clng
    wph
    @37
    simpr
    #
    fveq2d
    isperp.l
    syl6eqr
    rneqd
    #
    eleq2d
    @38
    @27
    @4
    @6
    @41
    eleq2d
    anbi12d
    @38
    @33
    @14
    vx
    vu
    @16
    @3
    @38
    @32
    @13
    vv
    @6
    @38
    @31
    @12
    @11
    @38
    @25
    cG
    crag
    @40
    fveq2d
    eleq2d
    ralbidv
    rexralbidv
    anbi12d
    opabbidv
    wph
    cG
    cstrkg
    wcel
    cG
    cvv
    wcel
    isperp.g
    cG
    cstrkg
    elex
    syl
    wph
    @19
    @4
    @4
    cxp
    #
    cvv
    wph
    @4
    cvv
    wcel
    #
    @43
    @42
    cvv
    wcel
    cL
    cvv
    wcel
    @43
    wph
    cL
    @39
    cvv
    isperp.l
    cG
    clng
    fvex
    eqeltri
    cL
    cvv
    rnexg
    mp1i
    #
    @44
    @4
    @4
    cvv
    cvv
    xpexg
    syl2anc
    @19
    @42
    wss
    wph
    @17
    va
    vb
    @4
    @4
    opabssxp
    a1i
    ssexd
    fvmptd
    eleq2d
    syl5bb
    wph
    cA
    @4
    wcel
    cB
    @4
    wcel
    @20
    @24
    wb
    isperp.a
    isperp.b
    @17
    @24
    va
    vb
    cA
    cB
    @4
    @4
    @3
    cA
    wceq
    #
    @6
    cB
    wceq
    #
    wa
    #
    @15
    @22
    vx
    @16
    @23
    @3
    cA
    @6
    cB
    ineq12
    @47
    @10
    @16
    wcel
    #
    wa
    #
    @14
    @21
    vu
    @3
    cA
    @45
    @46
    @48
    simpll
    @49
    @9
    @3
    wcel
    #
    wa
    @13
    vv
    @6
    cB
    @45
    @46
    @48
    @50
    simpllr
    raleqdv
    raleqbidva
    rexeqbidva
    opelopab2a
    syl2anc
    bitrd
end
