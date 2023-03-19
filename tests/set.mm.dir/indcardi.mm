include "cdom.mm"
include "wbr.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "domrefg.mm"
include "syl.mm"
include "wi.mm"
include "cfv.mm"
include "con0.mm"
include "cardon.mm"
include "a1i.mm"
include "wss.mm"
include "wa.mm"
include "wal.mm"
include "w3a.mm"
include "csdm.mm"
include "simpl1.mm"
include "simpr.mm"
include "wb.mm"
include "sdomdom.mm"
include "adantl.mm"
include "simpl3.mm"
include "domtr.mm"
include "syl2anc.mm"
include "numdom.mm"
include "cardsdom2.mm"
include "mpbird.mm"
include "id.mm"
include "com3l.mm"
include "sylc.mm"
include "ex.mm"
include "com23.mm"
include "alimdv.mm"
include "3exp.mm"
include "com34.mm"
include "3imp1.mm"
include "syl3anc.mm"
include "weq.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "cv.mm"
include "wceq.mm"
include "fveq2d.mm"
include "tfisi.mm"
include "mpd.mm"

theorem indcardi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cV: class V
  assume indcardi.a: |- ( ph -> A e. V )
  assume indcardi.b: |- ( ph -> T e. dom card )
  assume indcardi.c: |- ( ( ph /\ R ~<_ T /\ A. y ( S ~< R -> ch ) ) -> ps )
  assume indcardi.d: |- ( x = y -> ( ps <-> ch ) )
  assume indcardi.e: |- ( x = A -> ( ps <-> th ) )
  assume indcardi.f: |- ( x = y -> R = S )
  assume indcardi.g: |- ( x = A -> R = T )

  disjoint x y
  disjoint T x
  disjoint T y
  disjoint A x
  disjoint S x
  disjoint ch x
  disjoint ph x
  disjoint ph y
  disjoint th x
  disjoint R y
  disjoint ps y
  assert |- ( ph -> th )

  proof
    wph
    cT
    cT
    cdom
    wbr
    #
    wth
    wph
    cT
    ccrd
    cdm
    #
    wcel
    #
    @0
    indcardi.b
    cT
    @1
    domrefg
    syl
    wph
    cR
    cT
    cdom
    wbr
    #
    wps
    wi
    cS
    cT
    cdom
    wbr
    #
    wch
    wi
    #
    @0
    wth
    wi
    vx
    vy
    cA
    cR
    ccrd
    cfv
    #
    cS
    ccrd
    cfv
    #
    cT
    ccrd
    cfv
    #
    cV
    indcardi.a
    @8
    con0
    wcel
    wph
    cT
    cardon
    a1i
    wph
    @6
    con0
    wcel
    @6
    @8
    wss
    wa
    #
    @7
    @6
    wcel
    #
    @5
    wi
    #
    vy
    wal
    #
    w3a
    #
    @3
    wps
    @13
    @3
    wa
    wph
    @3
    cS
    cR
    csdm
    wbr
    #
    wch
    wi
    #
    vy
    wal
    #
    wps
    wph
    @9
    @12
    @3
    simpl1
    @13
    @3
    simpr
    wph
    @9
    @12
    @3
    @16
    wph
    @9
    @3
    @12
    @16
    wph
    @9
    @3
    @12
    @16
    wi
    wph
    @9
    @3
    w3a
    #
    @11
    @15
    vy
    @17
    @14
    @11
    wch
    @17
    @14
    @11
    wch
    wi
    #
    @17
    @14
    wa
    #
    @10
    @4
    @18
    @19
    @10
    @14
    @17
    @14
    simpr
    @19
    cS
    @1
    wcel
    #
    cR
    @1
    wcel
    #
    @10
    @14
    wb
    @19
    @2
    @4
    @20
    @19
    wph
    @2
    wph
    @9
    @3
    @14
    simpl1
    indcardi.b
    syl
    #
    @19
    cS
    cR
    cdom
    wbr
    #
    @3
    @4
    @14
    @23
    @17
    cS
    cR
    sdomdom
    adantl
    wph
    @9
    @3
    @14
    simpl3
    #
    cS
    cR
    cT
    domtr
    syl2anc
    #
    cT
    cS
    numdom
    syl2anc
    @19
    @2
    @3
    @21
    @22
    @24
    cT
    cR
    numdom
    syl2anc
    cS
    cR
    cardsdom2
    syl2anc
    mpbird
    @25
    @11
    @10
    @4
    wch
    @11
    id
    com3l
    sylc
    ex
    com23
    alimdv
    3exp
    com34
    3imp1
    indcardi.c
    syl3anc
    ex
    vx
    vy
    weq
    #
    @3
    @4
    wps
    wch
    @26
    cR
    cS
    cT
    cdom
    indcardi.f
    breq1d
    indcardi.d
    imbi12d
    vx
    cv
    cA
    wceq
    #
    @3
    @0
    wps
    wth
    @27
    cR
    cT
    cT
    cdom
    indcardi.g
    breq1d
    indcardi.e
    imbi12d
    @26
    cR
    cS
    ccrd
    indcardi.f
    fveq2d
    @27
    cR
    cT
    ccrd
    indcardi.g
    fveq2d
    tfisi
    mpd
end
