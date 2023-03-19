include "wbr.mm"
include "cv.mm"
include "wsbc.mm"
include "cfn.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "cvv.mm"
include "wa.mm"
include "wrel.mm"
include "brrelex12.mm"
include "mpan.mm"
include "simpl.mm"
include "wceq.mm"
include "simplr.mm"
include "wb.mm"
include "breq12.mm"
include "adantll.mm"
include "sbcied.mm"
include "biimprcd.mm"
include "mpd.mm"
include "csn.mm"
include "cdif.mm"
include "vex.mm"
include "sbc2ie.mm"
include "difexg.mm"
include "ax-mp.mm"
include "elexi.mm"
include "sylibr.mm"
include "sylanb.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cn0.mm"
include "w3a.mm"
include "3anbi1i.mm"
include "anbi2i.mm"
include "fi1uzind.mm"
include "syl3an1.mm"

theorem brfi1uzind
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
  assume brfi1uzind.r: |- Rel G
  assume brfi1uzind.f: |- F e. _V
  assume brfi1uzind.l: |- L e. NN0
  assume brfi1uzind.1: |- ( ( v = V /\ e = E ) -> ( ps <-> ph ) )
  assume brfi1uzind.2: |- ( ( v = w /\ e = f ) -> ( ps <-> th ) )
  assume brfi1uzind.3: |- ( ( v G e /\ n e. v ) -> ( v \ { n } ) G F )
  assume brfi1uzind.4: |- ( ( w = ( v \ { n } ) /\ f = F ) -> ( th <-> ch ) )
  assume brfi1uzind.base: |- ( ( v G e /\ ( # ` v ) = L ) -> ps )
  assume brfi1uzind.step: |- ( ( ( ( y + 1 ) e. NN0 /\ ( v G e /\ ( # ` v ) = ( y + 1 ) /\ n e. v ) ) /\ ch ) -> ps )

  disjoint E e
  disjoint E n
  disjoint E v
  disjoint e n
  disjoint e v
  disjoint n v
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
  disjoint e y
  disjoint f n
  disjoint f v
  disjoint f y
  disjoint n w
  disjoint n y
  disjoint v w
  disjoint v y
  disjoint w y
  disjoint L e
  disjoint L n
  disjoint L v
  disjoint L y
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
  disjoint E a
  disjoint E b
  disjoint a b
  disjoint F a
  disjoint F b
  disjoint a f
  disjoint a w
  disjoint b f
  disjoint b w
  disjoint G a
  disjoint G b
  disjoint a e
  disjoint a n
  disjoint a v
  disjoint a y
  disjoint b e
  disjoint b n
  disjoint b v
  disjoint b y
  disjoint V a
  disjoint V b
  assert |- ( ( V G E /\ V e. Fin /\ L <_ ( # ` V ) ) -> ph )

  proof
    cV
    cE
    cG
    wbr
    #
    va
    cv
    #
    vb
    cv
    #
    cG
    wbr
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
    cL
    cV
    chash
    cfv
    cle
    wbr
    wph
    @0
    cV
    cvv
    wcel
    #
    cE
    cvv
    wcel
    #
    wa
    #
    @5
    cG
    wrel
    @0
    @8
    brfi1uzind.r
    cV
    cE
    cG
    brrelex12
    mpan
    @8
    @5
    @0
    @8
    @4
    @0
    va
    cV
    cvv
    @6
    @7
    simpl
    @8
    @1
    cV
    wceq
    #
    wa
    @3
    @0
    vb
    cE
    cvv
    @6
    @7
    @9
    simplr
    @9
    @2
    cE
    wceq
    @3
    @0
    wb
    @8
    @1
    cV
    @2
    cE
    cG
    breq12
    adantll
    sbcied
    sbcied
    biimprcd
    mpd
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
    brfi1uzind.f
    brfi1uzind.l
    brfi1uzind.1
    brfi1uzind.2
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
    @11
    @10
    cG
    wbr
    #
    vn
    cv
    #
    @11
    wcel
    #
    @3
    vb
    cF
    wsbc
    va
    @11
    @14
    csn
    #
    cdif
    #
    wsbc
    #
    @3
    @13
    va
    vb
    @11
    @10
    vv
    vex
    #
    ve
    vex
    @1
    @11
    @2
    @10
    cG
    breq12
    sbc2ie
    #
    @13
    @15
    wa
    @17
    cF
    cG
    wbr
    #
    @18
    brfi1uzind.3
    @3
    @21
    va
    vb
    @17
    cF
    @11
    cvv
    wcel
    @17
    cvv
    wcel
    @19
    @11
    @16
    cvv
    difexg
    ax-mp
    cF
    cvv
    brfi1uzind.f
    elexi
    @1
    @17
    @2
    cF
    cG
    breq12
    sbc2ie
    sylibr
    sylanb
    brfi1uzind.4
    @12
    @13
    @11
    chash
    cfv
    #
    cL
    wceq
    wps
    @20
    brfi1uzind.base
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
    @12
    @22
    @23
    wceq
    #
    @15
    w3a
    #
    wa
    @24
    @13
    @25
    @15
    w3a
    #
    wa
    wch
    wps
    @26
    @27
    @24
    @12
    @13
    @25
    @15
    @20
    3anbi1i
    anbi2i
    brfi1uzind.step
    sylanb
    fi1uzind
    syl3an1
end
