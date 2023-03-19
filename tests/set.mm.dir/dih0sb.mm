include "ccnv.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "dih0rn.mm"
include "syl.mm"
include "dihcnv11.mm"
include "dih0cnv.mm"
include "eqeq2d.mm"
include "bitr3d.mm"

theorem dih0sb
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  assume dih0sb.h: |- H = ( LHyp ` K )
  assume dih0sb.o: |- .0. = ( 0. ` K )
  assume dih0sb.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dih0sb.u: |- U = ( ( DVecH ` K ) ` W )
  assume dih0sb.v: |- V = ( Base ` U )
  assume dih0sb.z: |- Z = ( 0g ` U )
  assume dih0sb.n: |- N = ( LSpan ` U )
  assume dih0sb.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dih0sb.x: |- ( ph -> X e. ran I )


  assert |- ( ph -> ( X = { Z } <-> ( `' I ` X ) = .0. ) )

  proof
    wph
    cX
    cI
    ccnv
    #
    cfv
    #
    cZ
    csn
    #
    @0
    cfv
    #
    wceq
    cX
    @2
    wceq
    @1
    c.0
    wceq
    wph
    cH
    cI
    cK
    cW
    cX
    @2
    dih0sb.h
    dih0sb.i
    dih0sb.k
    dih0sb.x
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @2
    cI
    crn
    wcel
    dih0sb.k
    cU
    cH
    cI
    cK
    cW
    cZ
    dih0sb.h
    dih0sb.i
    dih0sb.u
    dih0sb.z
    dih0rn
    syl
    dihcnv11
    wph
    @3
    c.0
    @1
    wph
    @4
    @3
    c.0
    wceq
    dih0sb.k
    cU
    cH
    cI
    cK
    cW
    c.0
    cZ
    dih0sb.h
    dih0sb.o
    dih0sb.i
    dih0sb.u
    dih0sb.z
    dih0cnv
    syl
    eqeq2d
    bitr3d
end
