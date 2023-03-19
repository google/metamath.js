include "cin.mm"
include "cfv.mm"
include "cun.mm"
include "co.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "wceq.mm"
include "crn.mm"
include "dihrnss.mm"
include "syl2anc.mm"
include "dochssv.mm"
include "dochdmj1.mm"
include "syl3anc.mm"
include "dochoc.mm"
include "ineq12d.mm"
include "eqtr2d.mm"
include "fveq2d.mm"
include "djhval2.mm"
include "eqtr4d.mm"

theorem dochdmm1
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dochdmm1.h: |- H = ( LHyp ` K )
  assume dochdmm1.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dochdmm1.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochdmm1.v: |- V = ( Base ` U )
  assume dochdmm1.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochdmm1.j: |- .\/ = ( ( joinH ` K ) ` W )
  assume dochdmm1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochdmm1.x: |- ( ph -> X e. ran I )
  assume dochdmm1.y: |- ( ph -> Y e. ran I )


  assert |- ( ph -> ( ._|_ ` ( X i^i Y ) ) = ( ( ._|_ ` X ) .\/ ( ._|_ ` Y ) ) )

  proof
    wph
    cX
    cY
    cin
    #
    c.pe
    cfv
    cX
    c.pe
    cfv
    #
    cY
    c.pe
    cfv
    #
    cun
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @1
    @2
    c.or
    co
    #
    wph
    @0
    @3
    c.pe
    wph
    @3
    @1
    c.pe
    cfv
    #
    @2
    c.pe
    cfv
    #
    cin
    #
    @0
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @1
    cV
    wss
    #
    @2
    cV
    wss
    #
    @3
    @8
    wceq
    dochdmm1.k
    wph
    @9
    cX
    cV
    wss
    #
    @10
    dochdmm1.k
    wph
    @9
    cX
    cI
    crn
    #
    wcel
    #
    @12
    dochdmm1.k
    dochdmm1.x
    cU
    cH
    cI
    cK
    cV
    cW
    cX
    dochdmm1.h
    dochdmm1.u
    dochdmm1.i
    dochdmm1.v
    dihrnss
    syl2anc
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    dochdmm1.h
    dochdmm1.u
    dochdmm1.v
    dochdmm1.o
    dochssv
    syl2anc
    #
    wph
    @9
    cY
    cV
    wss
    #
    @11
    dochdmm1.k
    wph
    @9
    cY
    @13
    wcel
    #
    @16
    dochdmm1.k
    dochdmm1.y
    cU
    cH
    cI
    cK
    cV
    cW
    cY
    dochdmm1.h
    dochdmm1.u
    dochdmm1.i
    dochdmm1.v
    dihrnss
    syl2anc
    cU
    cH
    cK
    c.pe
    cV
    cW
    cY
    dochdmm1.h
    dochdmm1.u
    dochdmm1.v
    dochdmm1.o
    dochssv
    syl2anc
    #
    cU
    cH
    cK
    c.pe
    cV
    cW
    @1
    @2
    dochdmm1.h
    dochdmm1.u
    dochdmm1.v
    dochdmm1.o
    dochdmj1
    syl3anc
    wph
    @6
    cX
    @7
    cY
    wph
    @9
    @14
    @6
    cX
    wceq
    dochdmm1.k
    dochdmm1.x
    cH
    cI
    cK
    c.pe
    cW
    cX
    dochdmm1.h
    dochdmm1.i
    dochdmm1.o
    dochoc
    syl2anc
    wph
    @9
    @17
    @7
    cY
    wceq
    dochdmm1.k
    dochdmm1.y
    cH
    cI
    cK
    c.pe
    cW
    cY
    dochdmm1.h
    dochdmm1.i
    dochdmm1.o
    dochoc
    syl2anc
    ineq12d
    eqtr2d
    fveq2d
    wph
    @9
    @10
    @11
    @5
    @4
    wceq
    dochdmm1.k
    @15
    @18
    cU
    cH
    c.or
    cK
    c.pe
    cV
    cW
    @1
    @2
    dochdmm1.h
    dochdmm1.u
    dochdmm1.v
    dochdmm1.o
    dochdmm1.j
    djhval2
    syl3anc
    eqtr4d
end
