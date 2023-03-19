include "cfv.mm"
include "wne.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "chlt.mm"
include "adantr.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "dochoc1.mm"
include "sylan9eqr.mm"
include "eqtr4d.mm"
include "ex.mm"
include "necon3d.mm"
include "wn.mm"
include "df-ne.mm"
include "dvhlvec.mm"
include "lkrshpor.mm"
include "orcomd.mm"
include "ord.mm"
include "syl5bi.mm"
include "syld.mm"
include "imp.mm"
include "dochshpncl.mm"
include "mpbid.mm"
include "necon1d.mm"
include "necon3ad.mm"
include "jcad.mm"
include "dochlkr.mm"
include "sylibrd.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lshpne.mm"
include "impbid.mm"

theorem dochkrshp
  let wph: wff ph
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cY: class Y
  assume dochkrshp.h: |- H = ( LHyp ` K )
  assume dochkrshp.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochkrshp.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochkrshp.v: |- V = ( Base ` U )
  assume dochkrshp.y: |- Y = ( LSHyp ` U )
  assume dochkrshp.f: |- F = ( LFnl ` U )
  assume dochkrshp.l: |- L = ( LKer ` U )
  assume dochkrshp.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochkrshp.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) =/= V <-> ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) e. Y ) )

  proof
    wph
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cV
    wne
    #
    @2
    cY
    wcel
    #
    wph
    @3
    @2
    @0
    wceq
    #
    @0
    cY
    wcel
    #
    wa
    @4
    wph
    @3
    @5
    @6
    wph
    @2
    @0
    @2
    cV
    wph
    @2
    @0
    wne
    #
    @2
    cV
    wceq
    #
    wph
    @7
    wa
    #
    @7
    @8
    wph
    @7
    simpr
    @9
    cU
    cH
    cK
    c.pe
    cV
    cW
    @0
    cY
    dochkrshp.h
    dochkrshp.o
    dochkrshp.u
    dochkrshp.v
    dochkrshp.y
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @7
    dochkrshp.k
    adantr
    wph
    @7
    @6
    wph
    @7
    @0
    cV
    wne
    #
    @6
    wph
    @0
    cV
    @2
    @0
    wph
    @0
    cV
    wceq
    #
    @5
    wph
    @11
    wa
    @2
    cV
    @0
    @11
    wph
    @2
    cV
    c.pe
    cfv
    #
    c.pe
    cfv
    cV
    @11
    @1
    @12
    c.pe
    @0
    cV
    c.pe
    fveq2
    fveq2d
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    dochkrshp.h
    dochkrshp.u
    dochkrshp.o
    dochkrshp.v
    dochkrshp.k
    dochoc1
    sylan9eqr
    #
    wph
    @11
    simpr
    eqtr4d
    ex
    necon3d
    @10
    @11
    wn
    #
    wph
    @6
    @0
    cV
    df-ne
    wph
    @11
    @6
    wph
    @6
    @11
    wph
    cF
    cG
    cY
    cL
    cV
    cU
    dochkrshp.v
    dochkrshp.y
    dochkrshp.f
    dochkrshp.l
    wph
    cU
    cH
    cK
    cW
    dochkrshp.h
    dochkrshp.u
    dochkrshp.k
    dvhlvec
    dochkrshp.g
    lkrshpor
    orcomd
    ord
    #
    syl5bi
    syld
    imp
    dochshpncl
    mpbid
    ex
    necon1d
    wph
    @3
    @14
    @6
    wph
    @11
    @2
    cV
    wph
    @11
    @8
    @13
    ex
    necon3ad
    @15
    syld
    jcad
    wph
    cU
    cF
    cG
    cH
    cK
    cL
    c.pe
    cW
    cY
    dochkrshp.h
    dochkrshp.o
    dochkrshp.u
    dochkrshp.f
    dochkrshp.y
    dochkrshp.l
    dochkrshp.k
    dochkrshp.g
    dochlkr
    sylibrd
    wph
    @4
    @3
    wph
    @4
    wa
    @2
    cY
    cV
    cU
    dochkrshp.v
    dochkrshp.y
    wph
    cU
    clmod
    wcel
    @4
    wph
    cU
    cH
    cK
    cW
    dochkrshp.h
    dochkrshp.u
    dochkrshp.k
    dvhlmod
    adantr
    wph
    @4
    simpr
    lshpne
    ex
    impbid
end
