include "cfv.mm"
include "wne.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "dochkrshp.mm"
include "dochlkr.mm"
include "bitrd.mm"

theorem dochkrshp2
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
  assume dochkrshp2.h: |- H = ( LHyp ` K )
  assume dochkrshp2.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochkrshp2.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochkrshp2.v: |- V = ( Base ` U )
  assume dochkrshp2.y: |- Y = ( LSHyp ` U )
  assume dochkrshp2.f: |- F = ( LFnl ` U )
  assume dochkrshp2.l: |- L = ( LKer ` U )
  assume dochkrshp2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochkrshp2.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) =/= V <-> ( ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) = ( L ` G ) /\ ( L ` G ) e. Y ) ) )

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
    cY
    wcel
    @1
    @0
    wceq
    @0
    cY
    wcel
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
    cY
    dochkrshp2.h
    dochkrshp2.o
    dochkrshp2.u
    dochkrshp2.v
    dochkrshp2.y
    dochkrshp2.f
    dochkrshp2.l
    dochkrshp2.k
    dochkrshp2.g
    dochkrshp
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
    dochkrshp2.h
    dochkrshp2.o
    dochkrshp2.u
    dochkrshp2.f
    dochkrshp2.y
    dochkrshp2.l
    dochkrshp2.k
    dochkrshp2.g
    dochlkr
    bitrd
end
