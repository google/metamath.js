include "cv.mm"
include "wf1o.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cen.mm"
include "wbr.mm"
include "wcel.mm"
include "enfixsn.mm"
include "syl3anc.mm"
include "wi.mm"
include "bren.mm"
include "sylib.mm"
include "w3a.mm"
include "cfsupp.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "ccnv.mm"
include "ccom.mm"
include "cmpt.mm"
include "eqid.mm"
include "f1ocnv.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "cvv.mm"
include "3ad2ant1.mm"
include "relen.mm"
include "brrelexi.mm"
include "syl.mm"
include "brrelex2i.mm"
include "mapfien.mm"
include "ovex.mm"
include "rabex2.mm"
include "f1oen.mm"
include "3adant3r.mm"
include "breq2.mm"
include "rabbidv.mm"
include "syl6eqr.mm"
include "adantl.mm"
include "3ad2ant3.mm"
include "breqtrd.mm"
include "3exp.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem mapfien2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cW: class W
  let c.0: class .0.
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume mapfien2.s: |- S = { x e. ( B ^m A ) | x finSupp .0. }
  assume mapfien2.t: |- T = { x e. ( D ^m C ) | x finSupp W }
  assume mapfien2.ac: |- ( ph -> A ~~ C )
  assume mapfien2.bd: |- ( ph -> B ~~ D )
  assume mapfien2.z: |- ( ph -> .0. e. B )
  assume mapfien2.w: |- ( ph -> W e. D )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint .0. x
  disjoint W x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint A z
  disjoint B w
  disjoint B z
  disjoint B y
  disjoint C w
  disjoint C z
  disjoint D w
  disjoint D z
  disjoint D y
  disjoint S w
  disjoint S y
  disjoint S z
  disjoint .0. w
  disjoint .0. y
  disjoint .0. z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint W z
  disjoint W y
  disjoint T y
  disjoint T z
  assert |- ( ph -> S ~~ T )

  proof
    wph
    cB
    cD
    vy
    cv
    #
    wf1o
    #
    c.0
    @0
    cfv
    #
    cW
    wceq
    #
    wa
    #
    vy
    wex
    #
    cS
    cT
    cen
    wbr
    #
    wph
    c.0
    cB
    wcel
    #
    cW
    cD
    wcel
    cB
    cD
    cen
    wbr
    #
    @5
    mapfien2.z
    mapfien2.w
    mapfien2.bd
    c.0
    cW
    vy
    cB
    cD
    enfixsn
    syl3anc
    wph
    @4
    @6
    vy
    wph
    cA
    cC
    vz
    cv
    #
    wf1o
    #
    vz
    wex
    #
    @4
    @6
    wi
    #
    wph
    cA
    cC
    cen
    wbr
    #
    @11
    mapfien2.ac
    cA
    cC
    vz
    bren
    sylib
    wph
    @10
    @12
    vz
    wph
    @10
    @4
    @6
    wph
    @10
    @4
    w3a
    cS
    vx
    cv
    #
    @2
    cfsupp
    wbr
    #
    vx
    cD
    cC
    cmap
    co
    #
    crab
    #
    cT
    cen
    wph
    @10
    @1
    cS
    @17
    cen
    wbr
    #
    @3
    wph
    @10
    @1
    w3a
    #
    cS
    @17
    vw
    cS
    @0
    vw
    cv
    @9
    ccnv
    #
    ccom
    ccom
    cmpt
    #
    wf1o
    @18
    @19
    vx
    cA
    cB
    cC
    cD
    cS
    @17
    vw
    @20
    @0
    @2
    c.0
    mapfien2.s
    @17
    eqid
    @2
    eqid
    @10
    wph
    cC
    cA
    @20
    wf1o
    @1
    cA
    cC
    @9
    f1ocnv
    3ad2ant2
    wph
    @10
    @1
    simp3
    @19
    @13
    cA
    cvv
    wcel
    wph
    @10
    @13
    @1
    mapfien2.ac
    3ad2ant1
    #
    cA
    cC
    cen
    relen
    brrelexi
    syl
    @19
    @8
    cB
    cvv
    wcel
    wph
    @10
    @8
    @1
    mapfien2.bd
    3ad2ant1
    #
    cB
    cD
    cen
    relen
    brrelexi
    syl
    @19
    @13
    cC
    cvv
    wcel
    @22
    cA
    cC
    cen
    relen
    brrelex2i
    syl
    @19
    @8
    cD
    cvv
    wcel
    @23
    cB
    cD
    cen
    relen
    brrelex2i
    syl
    wph
    @10
    @7
    @1
    mapfien2.z
    3ad2ant1
    mapfien
    cS
    @17
    @21
    @14
    c.0
    cfsupp
    wbr
    vx
    cB
    cA
    cmap
    co
    cS
    mapfien2.s
    cB
    cA
    cmap
    ovex
    rabex2
    f1oen
    syl
    3adant3r
    @4
    wph
    @17
    cT
    wceq
    #
    @10
    @3
    @24
    @1
    @3
    @17
    @14
    cW
    cfsupp
    wbr
    #
    vx
    @16
    crab
    cT
    @3
    @15
    @25
    vx
    @16
    @2
    cW
    @14
    cfsupp
    breq2
    rabbidv
    mapfien2.t
    syl6eqr
    adantl
    3ad2ant3
    breqtrd
    3exp
    exlimdv
    mpd
    exlimdv
    mpd
end
