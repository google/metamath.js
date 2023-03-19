include "cfv.mm"
include "cbs.mm"
include "wne.mm"
include "clsh.mm"
include "wcel.mm"
include "csn.mm"
include "eqid.mm"
include "dochkrshp.mm"
include "dvhlmod.mm"
include "lkrssv.mm"
include "dochn0nv.mm"
include "clss.mm"
include "chlt.mm"
include "wa.mm"
include "wss.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "dochsatshpb.mm"
include "3bitr4d.mm"

theorem dochkrsat
  let wph: wff ph
  let cA: class A
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  let c.0: class .0.
  assume dochkrsat.h: |- H = ( LHyp ` K )
  assume dochkrsat.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochkrsat.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochkrsat.a: |- A = ( LSAtoms ` U )
  assume dochkrsat.f: |- F = ( LFnl ` U )
  assume dochkrsat.l: |- L = ( LKer ` U )
  assume dochkrsat.z: |- .0. = ( 0g ` U )
  assume dochkrsat.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochkrsat.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( ._|_ ` ( L ` G ) ) =/= { .0. } <-> ( ._|_ ` ( L ` G ) ) e. A ) )

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
    cU
    cbs
    cfv
    #
    wne
    @2
    cU
    clsh
    cfv
    #
    wcel
    @1
    c.0
    csn
    wne
    @1
    cA
    wcel
    wph
    cU
    cF
    cG
    cH
    cK
    cL
    c.pe
    @3
    cW
    @4
    dochkrsat.h
    dochkrsat.o
    dochkrsat.u
    @3
    eqid
    #
    @4
    eqid
    #
    dochkrsat.f
    dochkrsat.l
    dochkrsat.k
    dochkrsat.g
    dochkrshp
    wph
    cU
    cH
    cK
    c.pe
    @3
    cW
    @0
    c.0
    dochkrsat.h
    dochkrsat.o
    dochkrsat.u
    @5
    dochkrsat.z
    dochkrsat.k
    wph
    cF
    cG
    cL
    @3
    cU
    @5
    dochkrsat.f
    dochkrsat.l
    wph
    cU
    cH
    cK
    cW
    dochkrsat.h
    dochkrsat.u
    dochkrsat.k
    dvhlmod
    dochkrsat.g
    lkrssv
    #
    dochn0nv
    wph
    cA
    @1
    cU
    clss
    cfv
    #
    cU
    cH
    cK
    c.pe
    cW
    @4
    dochkrsat.h
    dochkrsat.o
    dochkrsat.u
    @8
    eqid
    #
    dochkrsat.a
    @6
    dochkrsat.k
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @0
    @3
    wss
    @1
    @8
    wcel
    dochkrsat.k
    @7
    @8
    cU
    cH
    cK
    c.pe
    @3
    cW
    @0
    dochkrsat.h
    dochkrsat.u
    @5
    @9
    dochkrsat.o
    dochlss
    syl2anc
    dochsatshpb
    3bitr4d
end
