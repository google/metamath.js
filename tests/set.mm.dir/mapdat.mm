include "cfv.mm"
include "wcel.mm"
include "c0g.mm"
include "csn.mm"
include "clcv.mm"
include "wbr.mm"
include "eqid.mm"
include "mapd0.mm"
include "dvhlvec.mm"
include "lsatcv0.mm"
include "clss.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lsssn0.mm"
include "syl.mm"
include "lsatlssel.mm"
include "mapdcv.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "lcdlvec.mm"
include "mapdcl2.mm"
include "lsat0cv.mm"
include "mpbird.mm"

theorem mapdat
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
  assume mapdat.q: |- ( ph -> Q e. A )


  assert |- ( ph -> ( M ` Q ) e. B )

  proof
    wph
    cQ
    cM
    cfv
    #
    cB
    wcel
    cC
    c0g
    cfv
    #
    csn
    #
    @0
    cC
    clcv
    cfv
    #
    wbr
    wph
    cU
    c0g
    cfv
    #
    csn
    #
    cM
    cfv
    #
    @2
    @0
    @3
    wph
    cC
    cU
    cH
    cK
    cM
    @4
    cW
    @1
    mapdat.h
    mapdat.m
    mapdat.u
    @4
    eqid
    #
    mapdat.c
    @1
    eqid
    #
    mapdat.k
    mapd0
    wph
    @5
    cQ
    cU
    clcv
    cfv
    #
    wbr
    @6
    @0
    @3
    wbr
    wph
    cA
    @9
    cQ
    cU
    @4
    @7
    mapdat.a
    @9
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    mapdat.h
    mapdat.u
    mapdat.k
    dvhlvec
    mapdat.q
    lsatcv0
    wph
    @9
    cC
    cU
    clss
    cfv
    #
    cU
    @3
    cH
    cK
    cM
    cW
    @5
    cQ
    mapdat.h
    mapdat.m
    mapdat.u
    @11
    eqid
    #
    @10
    mapdat.c
    @3
    eqid
    #
    mapdat.k
    wph
    cU
    clmod
    wcel
    @5
    @11
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
    #
    @11
    cU
    @4
    @7
    @12
    lsssn0
    syl
    wph
    cA
    @11
    cQ
    cU
    @12
    mapdat.a
    @14
    mapdat.q
    lsatlssel
    #
    mapdcv
    mpbid
    eqbrtrrd
    wph
    cB
    @3
    cC
    clss
    cfv
    #
    @0
    cC
    @1
    @8
    @16
    eqid
    #
    mapdat.b
    @13
    wph
    cC
    cH
    cK
    cW
    mapdat.h
    mapdat.c
    mapdat.k
    lcdlvec
    wph
    cC
    cQ
    @11
    @16
    cU
    cH
    cK
    cM
    cW
    mapdat.h
    mapdat.m
    mapdat.u
    @12
    mapdat.c
    @17
    mapdat.k
    @15
    mapdcl2
    lsat0cv
    mpbird
end
