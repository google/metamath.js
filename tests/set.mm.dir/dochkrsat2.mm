include "cfv.mm"
include "c0g.mm"
include "csn.mm"
include "wne.mm"
include "wcel.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "lkrssv.mm"
include "dochn0nv.mm"
include "dochkrsat.mm"
include "bitr3d.mm"

theorem dochkrsat2
  let wph: wff ph
  let cA: class A
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  assume dochkrsat2.h: |- H = ( LHyp ` K )
  assume dochkrsat2.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochkrsat2.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochkrsat2.v: |- V = ( Base ` U )
  assume dochkrsat2.a: |- A = ( LSAtoms ` U )
  assume dochkrsat2.f: |- F = ( LFnl ` U )
  assume dochkrsat2.l: |- L = ( LKer ` U )
  assume dochkrsat2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochkrsat2.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) =/= V <-> ( ._|_ ` ( L ` G ) ) e. A ) )

  proof
    wph
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    cU
    c0g
    cfv
    #
    csn
    wne
    @1
    c.pe
    cfv
    cV
    wne
    @1
    cA
    wcel
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    @0
    @2
    dochkrsat2.h
    dochkrsat2.o
    dochkrsat2.u
    dochkrsat2.v
    @2
    eqid
    #
    dochkrsat2.k
    wph
    cF
    cG
    cL
    cV
    cU
    dochkrsat2.v
    dochkrsat2.f
    dochkrsat2.l
    wph
    cU
    cH
    cK
    cW
    dochkrsat2.h
    dochkrsat2.u
    dochkrsat2.k
    dvhlmod
    dochkrsat2.g
    lkrssv
    dochn0nv
    wph
    cA
    cU
    cF
    cG
    cH
    cK
    cL
    c.pe
    cW
    @2
    dochkrsat2.h
    dochkrsat2.o
    dochkrsat2.u
    dochkrsat2.a
    dochkrsat2.f
    dochkrsat2.l
    @3
    dochkrsat2.k
    dochkrsat2.g
    dochkrsat
    bitr3d
end
