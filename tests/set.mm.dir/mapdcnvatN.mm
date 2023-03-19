include "ccnv.mm"
include "cfv.mm"
include "wcel.mm"
include "c0g.mm"
include "csn.mm"
include "clcv.mm"
include "wbr.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lsssn0.mm"
include "syl.mm"
include "mapdcnvid1N.mm"
include "mapd0.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "lcdlvec.mm"
include "lsatcv0.mm"
include "crn.mm"
include "lcdlmod.mm"
include "mapdrn2.mm"
include "eleqtrrd.mm"
include "mapdcnvid2.mm"
include "lsatlssel.mm"
include "3brtr4d.mm"
include "mapdcnvcl.mm"
include "mapdcv.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "dvhlvec.mm"
include "lsat0cv.mm"

theorem mapdcnvatN
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  assume mapdat.h: |- H = ( LHyp ` K )
  assume mapdat.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdat.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdat.a: |- A = ( LSAtoms ` U )
  assume mapdat.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdat.b: |- B = ( LSAtoms ` C )
  assume mapdat.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdcnvat.q: |- ( ph -> Q e. B )


  assert |- ( ph -> ( `' M ` Q ) e. A )

  proof
    wph
    cQ
    cM
    ccnv
    #
    cfv
    #
    cA
    wcel
    cU
    c0g
    cfv
    #
    csn
    #
    @1
    cU
    clcv
    cfv
    #
    wbr
    wph
    @3
    cC
    c0g
    cfv
    #
    csn
    #
    @0
    cfv
    #
    @1
    @4
    wph
    @3
    cM
    cfv
    #
    @0
    cfv
    @3
    @7
    wph
    cU
    clss
    cfv
    #
    cU
    cH
    cK
    cM
    cW
    @3
    mapdat.h
    mapdat.m
    mapdat.u
    @9
    eqid
    #
    mapdat.k
    wph
    cU
    clmod
    wcel
    @3
    @9
    wcel
    wph
    cU
    cH
    cK
    cW
    mapdat.h
    mapdat.u
    mapdat.k
    dvhlmod
    @9
    cU
    @2
    @2
    eqid
    #
    @10
    lsssn0
    syl
    mapdcnvid1N
    wph
    @8
    @6
    @0
    wph
    cC
    cU
    cH
    cK
    cM
    @2
    cW
    @5
    mapdat.h
    mapdat.m
    mapdat.u
    @11
    mapdat.c
    @5
    eqid
    #
    mapdat.k
    mapd0
    fveq2d
    eqtr3d
    wph
    @7
    @1
    @4
    wbr
    @7
    cM
    cfv
    #
    @1
    cM
    cfv
    #
    cC
    clcv
    cfv
    #
    wbr
    wph
    @6
    cQ
    @13
    @14
    @15
    wph
    cB
    @15
    cQ
    cC
    @5
    @12
    mapdat.b
    @15
    eqid
    #
    wph
    cC
    cH
    cK
    cW
    mapdat.h
    mapdat.c
    mapdat.k
    lcdlvec
    mapdcnvat.q
    lsatcv0
    wph
    cH
    cK
    cM
    cW
    @6
    mapdat.h
    mapdat.m
    mapdat.k
    wph
    @6
    cC
    clss
    cfv
    #
    cM
    crn
    #
    wph
    cC
    clmod
    wcel
    @6
    @17
    wcel
    wph
    cC
    cH
    cK
    cW
    mapdat.h
    mapdat.c
    mapdat.k
    lcdlmod
    #
    @17
    cC
    @5
    @12
    @17
    eqid
    #
    lsssn0
    syl
    wph
    cC
    @17
    cH
    cK
    cM
    cW
    mapdat.h
    mapdat.m
    mapdat.c
    @20
    mapdat.k
    mapdrn2
    #
    eleqtrrd
    #
    mapdcnvid2
    wph
    cH
    cK
    cM
    cW
    cQ
    mapdat.h
    mapdat.m
    mapdat.k
    wph
    cQ
    @17
    @18
    wph
    cB
    @17
    cQ
    cC
    @20
    mapdat.b
    @19
    mapdcnvat.q
    lsatlssel
    @21
    eleqtrrd
    #
    mapdcnvid2
    3brtr4d
    wph
    @4
    cC
    @9
    cU
    @15
    cH
    cK
    cM
    cW
    @7
    @1
    mapdat.h
    mapdat.m
    mapdat.u
    @10
    @4
    eqid
    #
    mapdat.c
    @16
    mapdat.k
    wph
    @9
    cU
    cH
    cK
    cM
    cW
    @6
    mapdat.h
    mapdat.m
    mapdat.u
    @10
    mapdat.k
    @22
    mapdcnvcl
    wph
    @9
    cU
    cH
    cK
    cM
    cW
    cQ
    mapdat.h
    mapdat.m
    mapdat.u
    @10
    mapdat.k
    @23
    mapdcnvcl
    #
    mapdcv
    mpbird
    eqbrtrd
    wph
    cA
    @4
    @9
    @1
    cU
    @2
    @11
    @10
    mapdat.a
    @24
    wph
    cU
    cH
    cK
    cW
    mapdat.h
    mapdat.u
    mapdat.k
    dvhlvec
    @25
    lsat0cv
    mpbird
end
