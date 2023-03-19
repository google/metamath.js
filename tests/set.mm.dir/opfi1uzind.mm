include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wsbc.mm"
include "cfn.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "cvv.mm"
include "a1i.mm"
include "wa.mm"
include "opeq12.mm"
include "eleq1d.mm"
include "sbcied.mm"
include "sbcieg.mm"
include "biimparc.mm"
include "3adant3.mm"
include "csn.mm"
include "cdif.mm"
include "vex.mm"
include "sbc2ie.mm"
include "sylanb.mm"
include "difexi.mm"
include "sylibr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cn0.mm"
include "w3a.mm"
include "3anbi1i.mm"
include "anbi2i.mm"
include "fi1uzind.mm"
include "syld3an1.mm"

theorem opfi1uzind
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let ve: setvar e
  let vf: setvar f
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cL: class L
  let cV: class V
  let va: setvar a
  let vb: setvar b
  assume opfi1uzind.e: |- E e. _V
  assume opfi1uzind.f: |- F e. _V
  assume opfi1uzind.l: |- L e. NN0
  assume opfi1uzind.1: |- ( ( v = V /\ e = E ) -> ( ps <-> ph ) )
  assume opfi1uzind.2: |- ( ( v = w /\ e = f ) -> ( ps <-> th ) )
  assume opfi1uzind.3: |- ( ( <. v , e >. e. G /\ n e. v ) -> <. ( v \ { n } ) , F >. e. G )
  assume opfi1uzind.4: |- ( ( w = ( v \ { n } ) /\ f = F ) -> ( th <-> ch ) )
  assume opfi1uzind.base: |- ( ( <. v , e >. e. G /\ ( # ` v ) = L ) -> ps )
  assume opfi1uzind.step: |- ( ( ( ( y + 1 ) e. NN0 /\ ( <. v , e >. e. G /\ ( # ` v ) = ( y + 1 ) /\ n e. v ) ) /\ ch ) -> ps )

  disjoint e n
  disjoint e v
  disjoint e y
  disjoint n v
  disjoint n y
  disjoint v y
  disjoint E e
  disjoint E n
  disjoint E v
  disjoint F f
  disjoint F w
  disjoint f w
  disjoint G e
  disjoint G f
  disjoint G n
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint e f
  disjoint e w
  disjoint f n
  disjoint f v
  disjoint f y
  disjoint n w
  disjoint v w
  disjoint w y
  disjoint V e
  disjoint V n
  disjoint V v
  disjoint f ps
  disjoint n ps
  disjoint ps w
  disjoint ps y
  disjoint e th
  disjoint n th
  disjoint th v
  disjoint ch f
  disjoint ch w
  disjoint e ph
  disjoint n ph
  disjoint ph v
  disjoint L e
  disjoint L n
  disjoint L v
  disjoint L y
  disjoint E a
  disjoint E b
  disjoint a b
  disjoint a e
  disjoint a n
  disjoint a v
  disjoint b e
  disjoint b n
  disjoint b v
  disjoint F a
  disjoint F b
  disjoint a f
  disjoint a w
  disjoint b f
  disjoint b w
  disjoint G a
  disjoint G b
  disjoint V a
  disjoint V b
  disjoint a y
  disjoint b y
  assert |- ( ( <. V , E >. e. G /\ V e. Fin /\ L <_ ( # ` V ) ) -> ph )

  proof
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    cG
    wcel
    #
    vb
    cE
    wsbc
    #
    va
    cV
    wsbc
    #
    cV
    cfn
    wcel
    #
    cV
    cE
    cop
    #
    cG
    wcel
    #
    cL
    cV
    chash
    cfv
    cle
    wbr
    #
    wph
    @8
    @6
    @5
    @9
    @6
    @5
    @8
    @4
    @8
    va
    cV
    cfn
    @0
    cV
    wceq
    #
    @3
    @8
    vb
    cE
    cvv
    cE
    cvv
    wcel
    @10
    opfi1uzind.e
    a1i
    @10
    @1
    cE
    wceq
    wa
    @2
    @7
    cG
    @0
    @1
    cV
    cE
    opeq12
    eleq1d
    sbcied
    sbcieg
    biimparc
    3adant3
    wph
    wps
    wch
    wth
    @3
    vy
    vw
    vv
    ve
    vf
    vn
    cE
    cF
    cL
    cV
    va
    vb
    opfi1uzind.f
    opfi1uzind.l
    opfi1uzind.1
    opfi1uzind.2
    @3
    vb
    ve
    cv
    #
    wsbc
    va
    vv
    cv
    #
    wsbc
    #
    vn
    cv
    #
    @12
    wcel
    #
    wa
    @12
    @14
    csn
    #
    cdif
    #
    cF
    cop
    #
    cG
    wcel
    #
    @3
    vb
    cF
    wsbc
    va
    @17
    wsbc
    @13
    @12
    @11
    cop
    #
    cG
    wcel
    #
    @15
    @19
    @3
    @21
    va
    vb
    @12
    @11
    vv
    vex
    #
    ve
    vex
    @0
    @12
    wceq
    @1
    @11
    wceq
    wa
    @2
    @20
    cG
    @0
    @1
    @12
    @11
    opeq12
    eleq1d
    sbc2ie
    #
    opfi1uzind.3
    sylanb
    @3
    @19
    va
    vb
    @17
    cF
    @12
    @16
    @22
    difexi
    opfi1uzind.f
    @0
    @17
    wceq
    @1
    cF
    wceq
    wa
    @2
    @18
    cG
    @0
    @1
    @17
    cF
    opeq12
    eleq1d
    sbc2ie
    sylibr
    opfi1uzind.4
    @13
    @21
    @12
    chash
    cfv
    #
    cL
    wceq
    wps
    @23
    opfi1uzind.base
    sylanb
    vy
    cv
    c1
    caddc
    co
    #
    cn0
    wcel
    #
    @13
    @24
    @25
    wceq
    #
    @15
    w3a
    #
    wa
    @26
    @21
    @27
    @15
    w3a
    #
    wa
    wch
    wps
    @28
    @29
    @26
    @13
    @21
    @27
    @15
    @23
    3anbi1i
    anbi2i
    opfi1uzind.step
    sylanb
    fi1uzind
    syld3an1
end
