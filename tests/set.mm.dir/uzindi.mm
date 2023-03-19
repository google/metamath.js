include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "eluzfz2.mm"
include "syl.mm"
include "wi.mm"
include "cfzo.mm"
include "cfn.mm"
include "ccrd.mm"
include "cdm.mm"
include "fzofi.mm"
include "finnum.mm"
include "mp1i.mm"
include "csdm.mm"
include "wbr.mm"
include "wal.mm"
include "cdom.mm"
include "wa.mm"
include "simpll.mm"
include "simpr.mm"
include "wss.mm"
include "elfzuz3.mm"
include "adantl.mm"
include "fzoss2.mm"
include "fzossfz.mm"
include "syl6ss.mm"
include "sselda.mm"
include "wpss.mm"
include "wn.mm"
include "elfzofz.mm"
include "3syl.mm"
include "fzonel.mm"
include "jctr.mm"
include "ssnelpss.mm"
include "sylc.mm"
include "php3.mm"
include "sylancr.mm"
include "id.mm"
include "com13.mm"
include "ex.mm"
include "com23.mm"
include "alimdv.mm"
include "imp31.mm"
include "syl3anc.mm"
include "3adant2.mm"
include "weq.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "cv.mm"
include "wceq.mm"
include "oveq2d.mm"
include "indcardi.mm"
include "mpd.mm"

theorem uzindi
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
  let cL: class L
  let cV: class V
  assume uzindi.a: |- ( ph -> A e. V )
  assume uzindi.b: |- ( ph -> T e. ( ZZ>= ` L ) )
  assume uzindi.c: |- ( ( ph /\ R e. ( L ... T ) /\ A. y ( S e. ( L ..^ R ) -> ch ) ) -> ps )
  assume uzindi.d: |- ( x = y -> ( ps <-> ch ) )
  assume uzindi.e: |- ( x = A -> ( ps <-> th ) )
  assume uzindi.f: |- ( x = y -> R = S )
  assume uzindi.g: |- ( x = A -> R = T )

  disjoint x y
  disjoint L x
  disjoint L y
  disjoint A x
  disjoint S x
  disjoint T x
  disjoint T y
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
    cL
    cT
    cfz
    co
    #
    wcel
    #
    wth
    wph
    cT
    cL
    cuz
    cfv
    wcel
    @1
    uzindi.b
    cL
    cT
    eluzfz2
    syl
    wph
    cR
    @0
    wcel
    #
    wps
    wi
    #
    cS
    @0
    wcel
    #
    wch
    wi
    #
    @1
    wth
    wi
    vx
    vy
    cA
    cL
    cR
    cfzo
    co
    #
    cL
    cS
    cfzo
    co
    #
    cL
    cT
    cfzo
    co
    #
    cV
    uzindi.a
    @8
    cfn
    wcel
    @8
    ccrd
    cdm
    wcel
    wph
    cL
    cT
    fzofi
    @8
    finnum
    mp1i
    wph
    @7
    @6
    csdm
    wbr
    #
    @5
    wi
    #
    vy
    wal
    #
    @3
    @6
    @8
    cdom
    wbr
    wph
    @11
    wa
    #
    @2
    wps
    @12
    @2
    wa
    wph
    @2
    cS
    @6
    wcel
    #
    wch
    wi
    #
    vy
    wal
    #
    wps
    wph
    @11
    @2
    simpll
    @12
    @2
    simpr
    wph
    @11
    @2
    @15
    wph
    @2
    @11
    @15
    wph
    @2
    @11
    @15
    wi
    wph
    @2
    wa
    #
    @10
    @14
    vy
    @16
    @13
    @10
    wch
    @16
    @13
    @10
    wch
    wi
    #
    @16
    @13
    wa
    #
    @4
    @9
    @17
    @16
    @6
    @0
    cS
    @16
    cT
    cR
    cuz
    cfv
    wcel
    #
    @6
    @0
    wss
    @2
    @19
    wph
    cR
    cL
    cT
    elfzuz3
    adantl
    @19
    @6
    @8
    @0
    cR
    cL
    cT
    fzoss2
    cL
    cT
    fzossfz
    syl6ss
    syl
    sselda
    @18
    @6
    cfn
    wcel
    @7
    @6
    wpss
    #
    @9
    cL
    cR
    fzofi
    @18
    @7
    @6
    wss
    #
    @13
    cS
    @7
    wcel
    wn
    #
    wa
    #
    @20
    @18
    cS
    cL
    cR
    cfz
    co
    wcel
    #
    cR
    cS
    cuz
    cfv
    wcel
    @21
    @13
    @24
    @16
    cS
    cL
    cR
    elfzofz
    adantl
    cS
    cL
    cR
    elfzuz3
    cS
    cL
    cR
    fzoss2
    3syl
    @13
    @23
    @16
    @13
    @22
    cL
    cS
    fzonel
    jctr
    adantl
    @7
    @6
    cS
    ssnelpss
    sylc
    @6
    @7
    php3
    sylancr
    @10
    @9
    @4
    wch
    @10
    id
    com13
    sylc
    ex
    com23
    alimdv
    ex
    com23
    imp31
    uzindi.c
    syl3anc
    ex
    3adant2
    vx
    vy
    weq
    #
    @2
    @4
    wps
    wch
    @25
    cR
    cS
    @0
    uzindi.f
    eleq1d
    uzindi.d
    imbi12d
    vx
    cv
    cA
    wceq
    #
    @2
    @1
    wps
    wth
    @26
    cR
    cT
    @0
    uzindi.g
    eleq1d
    uzindi.e
    imbi12d
    @25
    cR
    cS
    cL
    cfzo
    uzindi.f
    oveq2d
    @26
    cR
    cT
    cL
    cfzo
    uzindi.g
    oveq2d
    indcardi
    mpd
end
