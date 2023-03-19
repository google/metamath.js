include "cv.mm"
include "cres.mm"
include "wf1o.mm"
include "crab.mm"
include "cdom.mm"
include "wbr.mm"
include "cpw.mm"
include "wcel.mm"
include "wa.mm"
include "cen.mm"
include "cvv.mm"
include "cfv.mm"
include "cmpt.mm"
include "vex.mm"
include "rabex.mm"
include "eqid.mm"
include "wceq.mm"
include "wfo.mm"
include "wf.mm"
include "fof.mm"
include "syl.mm"
include "feqmptd.mm"
include "ad2antrr.mm"
include "reseq1d.mm"
include "wss.mm"
include "elpwi.mm"
include "ad2antlr.mm"
include "resmptd.mm"
include "eqtrd.mm"
include "f1oeq1.mm"
include "biimpa.mm"
include "sylancom.mm"
include "w3a.mm"
include "wb.mm"
include "simp1ll.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "sseldd.mm"
include "simp3.mm"
include "syl3anc.mm"
include "f1oresrab.mm"
include "f1oeng.mm"
include "sylancr.mm"
include "ensymd.mm"
include "rabexg.mm"
include "rabss2.mm"
include "ssdomg.mm"
include "sylc.mm"
include "endomtr.mm"
include "syl2anc.mm"
include "wrex.mm"
include "foresf1o.mm"
include "r19.29a.mm"

theorem rabfodom
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let va: setvar a
  assume rabfodom.1: |- ( ( ph /\ x e. A /\ y = ( F ` x ) ) -> ( ch <-> ps ) )
  assume rabfodom.2: |- ( ph -> A e. V )
  assume rabfodom.3: |- ( ph -> F : A -onto-> B )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint V x
  disjoint V y
  disjoint ph x
  disjoint ph y
  disjoint ps y
  disjoint ch x
  disjoint A a
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint F a
  disjoint V a
  disjoint a ph
  disjoint a ps
  disjoint a ch
  assert |- ( ph -> { y e. B | ch } ~<_ { x e. A | ps } )

  proof
    wph
    va
    cv
    #
    cB
    cF
    @0
    cres
    #
    wf1o
    #
    wch
    vy
    cB
    crab
    #
    wps
    vx
    cA
    crab
    #
    cdom
    wbr
    #
    va
    cA
    cpw
    #
    wph
    @0
    @6
    wcel
    #
    wa
    #
    @2
    wa
    #
    @3
    wps
    vx
    @0
    crab
    #
    cen
    wbr
    @10
    @4
    cdom
    wbr
    #
    @5
    @9
    @10
    @3
    @9
    @10
    cvv
    wcel
    @10
    @3
    vx
    @0
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    @10
    cres
    #
    wf1o
    @10
    @3
    cen
    wbr
    wps
    vx
    @0
    va
    vex
    rabex
    @9
    wps
    wch
    vx
    vy
    @0
    cB
    @13
    @14
    @14
    eqid
    @8
    @2
    @1
    @14
    wceq
    #
    @0
    cB
    @14
    wf1o
    #
    @9
    @1
    vx
    cA
    @13
    cmpt
    #
    @0
    cres
    @14
    @9
    cF
    @18
    @0
    wph
    cF
    @18
    wceq
    @7
    @2
    wph
    vx
    cA
    cB
    cF
    wph
    cA
    cB
    cF
    wfo
    #
    cA
    cB
    cF
    wf
    rabfodom.3
    cA
    cB
    cF
    fof
    syl
    feqmptd
    ad2antrr
    reseq1d
    @9
    vx
    cA
    @0
    @13
    @7
    @0
    cA
    wss
    #
    wph
    @2
    @0
    cA
    elpwi
    ad2antlr
    #
    resmptd
    eqtrd
    @16
    @2
    @17
    @0
    cB
    @1
    @14
    f1oeq1
    biimpa
    sylancom
    @9
    @12
    @0
    wcel
    #
    vy
    cv
    @13
    wceq
    #
    w3a
    #
    wph
    @12
    cA
    wcel
    @23
    wch
    wps
    wb
    wph
    @7
    @2
    @22
    @23
    simp1ll
    @24
    @0
    cA
    @12
    @9
    @22
    @20
    @23
    @21
    3ad2ant1
    @9
    @22
    @23
    simp2
    sseldd
    @9
    @22
    @23
    simp3
    rabfodom.1
    syl3anc
    f1oresrab
    @10
    @3
    cvv
    @15
    f1oeng
    sylancr
    ensymd
    @9
    @4
    cvv
    wcel
    #
    @10
    @4
    wss
    #
    @11
    wph
    @25
    @7
    @2
    wph
    cA
    cV
    wcel
    #
    @25
    rabfodom.2
    wps
    vx
    cA
    cV
    rabexg
    syl
    ad2antrr
    @9
    @20
    @26
    @21
    wps
    vx
    @0
    cA
    rabss2
    syl
    @10
    @4
    cvv
    ssdomg
    sylc
    @3
    @10
    @4
    endomtr
    syl2anc
    wph
    @27
    @19
    @2
    va
    @6
    wrex
    rabfodom.2
    rabfodom.3
    va
    cA
    cB
    cF
    cV
    foresf1o
    syl2anc
    r19.29a
end
