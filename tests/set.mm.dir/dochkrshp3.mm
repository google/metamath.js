include "cfv.mm"
include "wne.mm"
include "wceq.mm"
include "clsh.mm"
include "wcel.mm"
include "wa.mm"
include "eqid.mm"
include "dochkrshp2.mm"
include "dvhlvec.mm"
include "lkrshp4.mm"
include "anbi2d.mm"
include "bitr4d.mm"

theorem dochkrshp3
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


  assert |- ( ph -> ( ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) =/= V <-> ( ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) = ( L ` G ) /\ ( L ` G ) =/= V ) ) )

  proof
    wph
    cG
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    #
    cV
    wne
    @1
    @0
    wceq
    #
    @0
    cU
    clsh
    cfv
    #
    wcel
    #
    wa
    @2
    @0
    cV
    wne
    #
    wa
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
    @3
    dochkrshp3.h
    dochkrshp3.o
    dochkrshp3.u
    dochkrshp3.v
    @3
    eqid
    #
    dochkrshp3.f
    dochkrshp3.l
    dochkrshp3.k
    dochkrshp3.g
    dochkrshp2
    wph
    @5
    @4
    @2
    wph
    cF
    cG
    @3
    cL
    cV
    cU
    dochkrshp3.v
    @6
    dochkrshp3.f
    dochkrshp3.l
    wph
    cU
    cH
    cK
    cW
    dochkrshp3.h
    dochkrshp3.u
    dochkrshp3.k
    dvhlvec
    dochkrshp3.g
    lkrshp4
    anbi2d
    bitr4d
end
