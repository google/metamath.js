include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdih.mm"
include "crn.mm"
include "wss.mm"
include "eqid.mm"
include "dochcl.mm"
include "syl2anc.mm"
include "dochoc.mm"
include "doch1.mm"
include "syl.mm"
include "eqeq12d.mm"
include "dochssv.mm"
include "dih1rn.mm"
include "doch11.mm"
include "bitr3d.mm"
include "necon3bid.mm"

theorem dochn0nv
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume dochn0nv.h: |- H = ( LHyp ` K )
  assume dochn0nv.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochn0nv.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochn0nv.v: |- V = ( Base ` U )
  assume dochn0nv.z: |- .0. = ( 0g ` U )
  assume dochn0nv.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochn0nv.x: |- ( ph -> X C_ V )


  assert |- ( ph -> ( ( ._|_ ` X ) =/= { .0. } <-> ( ._|_ ` ( ._|_ ` X ) ) =/= V ) )

  proof
    wph
    cX
    c.pe
    cfv
    #
    c.0
    csn
    #
    @0
    c.pe
    cfv
    #
    cV
    wph
    @2
    c.pe
    cfv
    #
    cV
    c.pe
    cfv
    #
    wceq
    @0
    @1
    wceq
    @2
    cV
    wceq
    wph
    @3
    @0
    @4
    @1
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @0
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    #
    wcel
    #
    @3
    @0
    wceq
    dochn0nv.k
    wph
    @5
    cX
    cV
    wss
    #
    @8
    dochn0nv.k
    dochn0nv.x
    cU
    cH
    @6
    cK
    c.pe
    cV
    cW
    cX
    dochn0nv.h
    @6
    eqid
    #
    dochn0nv.u
    dochn0nv.v
    dochn0nv.o
    dochcl
    syl2anc
    cH
    @6
    cK
    c.pe
    cW
    @0
    dochn0nv.h
    @10
    dochn0nv.o
    dochoc
    syl2anc
    wph
    @5
    @4
    @1
    wceq
    dochn0nv.k
    cU
    cH
    cK
    c.pe
    cV
    cW
    c.0
    dochn0nv.h
    dochn0nv.u
    dochn0nv.o
    dochn0nv.v
    dochn0nv.z
    doch1
    syl
    eqeq12d
    wph
    cH
    @6
    cK
    c.pe
    cW
    @2
    cV
    dochn0nv.h
    @10
    dochn0nv.o
    dochn0nv.k
    wph
    @5
    @0
    cV
    wss
    #
    @2
    @7
    wcel
    dochn0nv.k
    wph
    @5
    @9
    @11
    dochn0nv.k
    dochn0nv.x
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    dochn0nv.h
    dochn0nv.u
    dochn0nv.v
    dochn0nv.o
    dochssv
    syl2anc
    cU
    cH
    @6
    cK
    c.pe
    cV
    cW
    @0
    dochn0nv.h
    @10
    dochn0nv.u
    dochn0nv.v
    dochn0nv.o
    dochcl
    syl2anc
    wph
    @5
    cV
    @7
    wcel
    dochn0nv.k
    cU
    cH
    @6
    cK
    cV
    cW
    dochn0nv.h
    @10
    dochn0nv.u
    dochn0nv.v
    dih1rn
    syl
    doch11
    bitr3d
    necon3bid
end
