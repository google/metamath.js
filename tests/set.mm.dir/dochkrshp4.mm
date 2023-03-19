include "cfv.mm"
include "wceq.mm"
include "wne.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "df-ne.mm"
include "dochkrshp3.mm"
include "biimprd.mm"
include "expdimp.mm"
include "syl5bir.mm"
include "orrd.mm"
include "orcomd.mm"
include "ex.mm"
include "simpl.mm"
include "syl6bi.mm"
include "dochoc1.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "impbid.mm"

theorem dochkrshp4
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
  assume dochkrshp3.h: |- H = ( LHyp ` K )
  assume dochkrshp3.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochkrshp3.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochkrshp3.v: |- V = ( Base ` U )
  assume dochkrshp3.f: |- F = ( LFnl ` U )
  assume dochkrshp3.l: |- L = ( LKer ` U )
  assume dochkrshp3.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochkrshp3.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) = ( L ` G ) <-> ( ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) =/= V \/ ( L ` G ) = V ) ) )

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
    @0
    wceq
    #
    @2
    cV
    wne
    #
    @0
    cV
    wceq
    #
    wo
    #
    wph
    @3
    @6
    wph
    @3
    wa
    #
    @5
    @4
    @7
    @5
    @4
    @5
    wn
    @0
    cV
    wne
    #
    @7
    @4
    @0
    cV
    df-ne
    wph
    @3
    @8
    @4
    wph
    @4
    @3
    @8
    wa
    #
    wph
    cU
    cF
    cG
    cH
    cK
    cL
    c.pe
    cV
    cW
    dochkrshp3.h
    dochkrshp3.o
    dochkrshp3.u
    dochkrshp3.v
    dochkrshp3.f
    dochkrshp3.l
    dochkrshp3.k
    dochkrshp3.g
    dochkrshp3
    #
    biimprd
    expdimp
    syl5bir
    orrd
    orcomd
    ex
    wph
    @4
    @3
    @5
    wph
    @4
    @9
    @3
    @10
    @3
    @8
    simpl
    syl6bi
    wph
    @3
    @5
    cV
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cV
    wceq
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    dochkrshp3.h
    dochkrshp3.u
    dochkrshp3.o
    dochkrshp3.v
    dochkrshp3.k
    dochoc1
    @5
    @2
    @12
    @0
    cV
    @5
    @1
    @11
    c.pe
    @0
    cV
    c.pe
    fveq2
    fveq2d
    @5
    id
    eqeq12d
    syl5ibrcom
    jaod
    impbid
end
