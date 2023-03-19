include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cec.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wb.mm"
include "ecopqsi.mm"
include "copab.mm"
include "df-br.mm"
include "eleq2i.mm"
include "bitri.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "4exbidv.mm"
include "anbi2d.mm"
include "opelopab2.mm"
include "syl5bb.mm"
include "syl2an.mm"
include "wi.mm"
include "opeq12.mm"
include "eceq1d.mm"
include "anim12i.mm"
include "cxp.mm"
include "opelxpi.mm"
include "opelxp.mm"
include "wer.mm"
include "a1i.mm"
include "id.mm"
include "ereldm.mm"
include "syl5bbr.mm"
include "syl5ibr.mm"
include "im2anan9.mm"
include "an4s.mm"
include "ex.mm"
include "com13.mm"
include "mpdd.mm"
include "pm5.74d.mm"
include "cgsex4g.mm"
include "eqcom.mm"
include "anbi12i.mm"
include "biimt.mm"
include "anbi12d.mm"
include "3bitr4d.mm"
include "bitrd.mm"

theorem brecop
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.sm: class .~
  let cG: class G
  let cH: class H
  let c.le: class .<_
  assume brecop.1: |- .~ e. _V
  assume brecop.2: |- .~ Er ( G X. G )
  assume brecop.4: |- H = ( ( G X. G ) /. .~ )
  assume brecop.5: |- .<_ = { <. x , y >. | ( ( x e. H /\ y e. H ) /\ E. z E. w E. v E. u ( ( x = [ <. z , w >. ] .~ /\ y = [ <. v , u >. ] .~ ) /\ ph ) ) }
  assume brecop.6: |- ( ( ( ( z e. G /\ w e. G ) /\ ( A e. G /\ B e. G ) ) /\ ( ( v e. G /\ u e. G ) /\ ( C e. G /\ D e. G ) ) ) -> ( ( [ <. z , w >. ] .~ = [ <. A , B >. ] .~ /\ [ <. v , u >. ] .~ = [ <. C , D >. ] .~ ) -> ( ph <-> ps ) ) )

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint A y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint A z
  disjoint v w
  disjoint u w
  disjoint A w
  disjoint u v
  disjoint A v
  disjoint A u
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint B v
  disjoint B u
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint C w
  disjoint C v
  disjoint C u
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint D w
  disjoint D v
  disjoint D u
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint .~ w
  disjoint .~ v
  disjoint .~ u
  disjoint H x
  disjoint H y
  disjoint G z
  disjoint G w
  disjoint G v
  disjoint G u
  disjoint ph x
  disjoint ph y
  disjoint ps z
  disjoint ps w
  disjoint ps v
  disjoint ps u
  assert |- ( ( ( A e. G /\ B e. G ) /\ ( C e. G /\ D e. G ) ) -> ( [ <. A , B >. ] .~ .<_ [ <. C , D >. ] .~ <-> ps ) )

  proof
    cA
    cG
    wcel
    cB
    cG
    wcel
    wa
    #
    cC
    cG
    wcel
    cD
    cG
    wcel
    wa
    #
    wa
    #
    cA
    cB
    cop
    #
    c.sm
    cec
    #
    cC
    cD
    cop
    #
    c.sm
    cec
    #
    c.le
    wbr
    #
    @4
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    c.sm
    cec
    #
    wceq
    #
    @6
    vv
    cv
    #
    vu
    cv
    #
    cop
    #
    c.sm
    cec
    #
    wceq
    #
    wa
    #
    wph
    wa
    #
    vu
    wex
    vv
    wex
    vw
    wex
    vz
    wex
    #
    wps
    @0
    @4
    cH
    wcel
    #
    @6
    cH
    wcel
    #
    @7
    @20
    wb
    @1
    cG
    cA
    cB
    c.sm
    cH
    brecop.1
    brecop.4
    ecopqsi
    cG
    cC
    cD
    c.sm
    cH
    brecop.1
    brecop.4
    ecopqsi
    @7
    @4
    @6
    cop
    #
    vx
    cv
    #
    cH
    wcel
    vy
    cv
    #
    cH
    wcel
    wa
    @24
    @11
    wceq
    #
    @25
    @16
    wceq
    #
    wa
    #
    wph
    wa
    #
    vu
    wex
    vv
    wex
    vw
    wex
    vz
    wex
    #
    wa
    vx
    vy
    copab
    #
    wcel
    #
    @21
    @22
    wa
    @20
    @7
    @23
    c.le
    wcel
    @32
    @4
    @6
    c.le
    df-br
    c.le
    @31
    @23
    brecop.5
    eleq2i
    bitri
    @30
    @12
    @27
    wa
    #
    wph
    wa
    #
    vu
    wex
    vv
    wex
    vw
    wex
    vz
    wex
    @20
    vx
    vy
    @4
    @6
    cH
    cH
    @24
    @4
    wceq
    #
    @29
    @34
    vz
    vw
    vv
    vu
    @35
    @28
    @33
    wph
    @35
    @26
    @12
    @27
    @24
    @4
    @11
    eqeq1
    anbi1d
    anbi1d
    4exbidv
    @25
    @6
    wceq
    #
    @34
    @19
    vz
    vw
    vv
    vu
    @36
    @33
    @18
    wph
    @36
    @27
    @17
    @12
    @25
    @6
    @16
    eqeq1
    anbi2d
    anbi1d
    4exbidv
    opelopab2
    syl5bb
    syl2an
    @2
    @11
    @4
    wceq
    #
    @16
    @6
    wceq
    #
    wa
    #
    @2
    wph
    wi
    #
    wa
    #
    vu
    wex
    vv
    wex
    vw
    wex
    vz
    wex
    @2
    wps
    wi
    #
    @20
    wps
    @40
    @42
    @39
    vz
    vw
    vv
    vu
    cA
    cB
    cC
    cD
    cG
    cG
    @8
    cA
    wceq
    @9
    cB
    wceq
    wa
    #
    @37
    @13
    cC
    wceq
    @14
    cD
    wceq
    wa
    #
    @38
    @43
    @10
    @3
    c.sm
    @8
    @9
    cA
    cB
    opeq12
    eceq1d
    @44
    @15
    @5
    c.sm
    @13
    @14
    cC
    cD
    opeq12
    eceq1d
    anim12i
    @39
    @2
    wph
    wps
    @39
    @2
    @8
    cG
    wcel
    @9
    cG
    wcel
    wa
    #
    @13
    cG
    wcel
    @14
    cG
    wcel
    wa
    #
    wa
    #
    wph
    wps
    wb
    #
    @37
    @0
    @45
    @38
    @1
    @46
    @0
    @45
    @37
    @3
    cG
    cG
    cxp
    #
    wcel
    #
    cA
    cB
    cG
    cG
    opelxpi
    @45
    @10
    @49
    wcel
    @37
    @50
    @8
    @9
    cG
    cG
    opelxp
    @37
    @10
    @3
    c.sm
    @49
    @49
    c.sm
    wer
    #
    @37
    brecop.2
    a1i
    @37
    id
    ereldm
    syl5bbr
    syl5ibr
    @1
    @46
    @38
    @5
    @49
    wcel
    #
    cC
    cD
    cG
    cG
    opelxpi
    @46
    @15
    @49
    wcel
    @38
    @52
    @13
    @14
    cG
    cG
    opelxp
    @38
    @15
    @5
    c.sm
    @49
    @51
    @38
    brecop.2
    a1i
    @38
    id
    ereldm
    syl5bbr
    syl5ibr
    im2anan9
    @47
    @2
    @39
    @48
    @47
    @2
    @39
    @48
    wi
    #
    @45
    @0
    @46
    @1
    @53
    brecop.6
    an4s
    ex
    com13
    mpdd
    pm5.74d
    cgsex4g
    @2
    @19
    @41
    vz
    vw
    vv
    vu
    @2
    @18
    @39
    wph
    @40
    @18
    @39
    wb
    @2
    @12
    @37
    @17
    @38
    @4
    @11
    eqcom
    @6
    @16
    eqcom
    anbi12i
    a1i
    @2
    wph
    biimt
    anbi12d
    4exbidv
    @2
    wps
    biimt
    3bitr4d
    bitrd
end
