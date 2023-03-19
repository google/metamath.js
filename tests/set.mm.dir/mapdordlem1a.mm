include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "wceq.mm"
include "simprr.mm"
include "chlt.mm"
include "adantr.mm"
include "simprl.mm"
include "dochlkr.mm"
include "mpbid.mm"
include "simpld.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "cv.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eleq1d.mm"
include "elrab2.mm"
include "lcfl1lem.mm"
include "anbi1i.mm"
include "anass.mm"
include "an12.mm"
include "3bitri.mm"
include "3bitr4g.mm"

theorem mapdordlem1a
  let wph: wff ph
  let cC: class C
  let cT: class T
  let cU: class U
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cO: class O
  let cV: class V
  let cW: class W
  let cY: class Y
  assume mapdordlem1a.h: |- H = ( LHyp ` K )
  assume mapdordlem1a.o: |- O = ( ( ocH ` K ) ` W )
  assume mapdordlem1a.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdordlem1a.v: |- V = ( Base ` U )
  assume mapdordlem1a.y: |- Y = ( LSHyp ` U )
  assume mapdordlem1a.f: |- F = ( LFnl ` U )
  assume mapdordlem1a.l: |- L = ( LKer ` U )
  assume mapdordlem1a.t: |- T = { g e. F | ( O ` ( O ` ( L ` g ) ) ) e. Y }
  assume mapdordlem1a.c: |- C = { g e. F | ( O ` ( O ` ( L ` g ) ) ) = ( L ` g ) }
  assume mapdordlem1a.k: |- ( ph -> ( K e. HL /\ W e. H ) )

  disjoint F g
  disjoint J g
  disjoint L g
  disjoint O g
  disjoint Y g
  assert |- ( ph -> ( J e. T <-> ( J e. C /\ ( O ` ( O ` ( L ` J ) ) ) e. Y ) ) )

  proof
    wph
    cJ
    cF
    wcel
    #
    cJ
    cL
    cfv
    #
    cO
    cfv
    #
    cO
    cfv
    #
    cY
    wcel
    #
    wa
    #
    @3
    @1
    wceq
    #
    @5
    wa
    #
    cJ
    cT
    wcel
    cJ
    cC
    wcel
    #
    @4
    wa
    #
    wph
    @5
    @6
    wph
    @5
    @6
    wph
    @5
    wa
    #
    @6
    @1
    cY
    wcel
    #
    @10
    @4
    @6
    @11
    wa
    wph
    @0
    @4
    simprr
    @10
    cU
    cF
    cJ
    cH
    cK
    cL
    cO
    cW
    cY
    mapdordlem1a.h
    mapdordlem1a.o
    mapdordlem1a.u
    mapdordlem1a.f
    mapdordlem1a.y
    mapdordlem1a.l
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @5
    mapdordlem1a.k
    adantr
    wph
    @0
    @4
    simprl
    dochlkr
    mpbid
    simpld
    ex
    pm4.71rd
    vg
    cv
    #
    cL
    cfv
    #
    cO
    cfv
    #
    cO
    cfv
    #
    cY
    wcel
    @4
    vg
    cJ
    cF
    cT
    @12
    cJ
    wceq
    #
    @15
    @3
    cY
    @16
    @14
    @2
    cO
    @16
    @13
    @1
    cO
    @12
    cJ
    cL
    fveq2
    fveq2d
    fveq2d
    eleq1d
    mapdordlem1a.t
    elrab2
    @9
    @0
    @6
    wa
    #
    @4
    wa
    @0
    @6
    @4
    wa
    wa
    @7
    @8
    @17
    @4
    cC
    vg
    cF
    cJ
    cL
    cO
    mapdordlem1a.c
    lcfl1lem
    anbi1i
    @0
    @6
    @4
    anass
    @0
    @6
    @4
    an12
    3bitri
    3bitr4g
end
