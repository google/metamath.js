include "crn.mm"
include "cuni.mm"
include "cld.mm"
include "cfv.mm"
include "clss.mm"
include "cpw.mm"
include "cin.mm"
include "eqid.mm"
include "mapdrn.mm"
include "unieqd.mm"
include "uniin.mm"
include "cbs.mm"
include "dvhlmod.mm"
include "lduallmod.mm"
include "lssuni.mm"
include "clmod.mm"
include "ldualvbase.mm"
include "eqtrd.mm"
include "wceq.mm"
include "unipw.mm"
include "a1i.mm"
include "ineq12d.mm"
include "wss.mm"
include "cv.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "syl5sseq.mm"
include "wcel.mm"
include "lclkr.mm"
include "clfn.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex2.mm"
include "pwid.mm"
include "elind.mm"
include "elssuni.mm"
include "syl.mm"
include "eqssd.mm"

theorem mapdunirnN
  let wph: wff ph
  let cC: class C
  let cU: class U
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cO: class O
  let cW: class W
  assume mapdrn.h: |- H = ( LHyp ` K )
  assume mapdrn.o: |- O = ( ( ocH ` K ) ` W )
  assume mapdrn.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdrn.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdrn.f: |- F = ( LFnl ` U )
  assume mapdrn.l: |- L = ( LKer ` U )
  assume mapdunirn.c: |- C = { g e. F | ( O ` ( O ` ( L ` g ) ) ) = ( L ` g ) }
  assume mapdunirn.k: |- ( ph -> ( K e. HL /\ W e. H ) )

  disjoint F g
  disjoint K g
  disjoint L g
  disjoint O g
  disjoint U g
  disjoint W g
  assert |- ( ph -> U. ran M = C )

  proof
    wph
    cM
    crn
    #
    cuni
    cU
    cld
    cfv
    #
    clss
    cfv
    #
    cC
    cpw
    #
    cin
    #
    cuni
    #
    cC
    wph
    @0
    @4
    wph
    cC
    @1
    @2
    cU
    vg
    cF
    cH
    cK
    cL
    cM
    cO
    cW
    mapdrn.h
    mapdrn.o
    mapdrn.m
    mapdrn.u
    mapdrn.f
    mapdrn.l
    @1
    eqid
    #
    @2
    eqid
    #
    mapdunirn.c
    mapdunirn.k
    mapdrn
    unieqd
    wph
    @5
    cC
    wph
    @2
    cuni
    #
    @3
    cuni
    #
    cin
    #
    @5
    cC
    @2
    @3
    uniin
    wph
    @10
    cF
    cC
    cin
    #
    cC
    wph
    @8
    cF
    @9
    cC
    wph
    @8
    @1
    cbs
    cfv
    #
    cF
    wph
    @2
    @12
    @1
    @12
    eqid
    #
    @7
    wph
    @1
    cU
    @6
    wph
    cU
    cH
    cK
    cW
    mapdrn.h
    mapdrn.u
    mapdunirn.k
    dvhlmod
    #
    lduallmod
    lssuni
    wph
    @1
    cF
    @12
    cU
    clmod
    mapdrn.f
    @6
    @13
    @14
    ldualvbase
    eqtrd
    @9
    cC
    wceq
    wph
    cC
    unipw
    a1i
    ineq12d
    @11
    cC
    wceq
    #
    wph
    cC
    cF
    wss
    @15
    cC
    vg
    cv
    cL
    cfv
    #
    cO
    cfv
    cO
    cfv
    @16
    wceq
    #
    vg
    cF
    crab
    cF
    mapdunirn.c
    @17
    vg
    cF
    ssrab2
    eqsstri
    cC
    cF
    sseqin2
    mpbi
    a1i
    eqtrd
    syl5sseq
    wph
    cC
    @4
    wcel
    cC
    @5
    wss
    wph
    @2
    @3
    cC
    wph
    cC
    @1
    @2
    cU
    vg
    cF
    cH
    cK
    cL
    cO
    cW
    mapdrn.h
    mapdrn.u
    mapdrn.o
    mapdrn.f
    mapdrn.l
    @6
    @7
    mapdunirn.c
    mapdunirn.k
    lclkr
    cC
    @3
    wcel
    wph
    cC
    @17
    vg
    cF
    cC
    mapdunirn.c
    cF
    cU
    clfn
    cfv
    cvv
    mapdrn.f
    cU
    clfn
    fvex
    eqeltri
    rabex2
    pwid
    a1i
    elind
    cC
    @4
    elssuni
    syl
    eqssd
    eqtrd
end
