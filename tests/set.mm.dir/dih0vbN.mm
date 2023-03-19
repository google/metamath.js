include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "dih0.mm"
include "syl.mm"
include "eqeq2d.mm"
include "clmod.mm"
include "wb.mm"
include "dvhlmod.mm"
include "lspsneq0.mm"
include "syl2anc.mm"
include "bitr2d.mm"

theorem dih0vbN
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
  assume dih0vb.h: |- H = ( LHyp ` K )
  assume dih0vb.o: |- .0. = ( 0. ` K )
  assume dih0vb.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dih0vb.u: |- U = ( ( DVecH ` K ) ` W )
  assume dih0vb.v: |- V = ( Base ` U )
  assume dih0vb.z: |- Z = ( 0g ` U )
  assume dih0vb.n: |- N = ( LSpan ` U )
  assume dih0vb.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dih0vb.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( X = Z <-> ( N ` { X } ) = ( I ` .0. ) ) )

  proof
    wph
    cX
    csn
    cN
    cfv
    #
    c.0
    cI
    cfv
    #
    wceq
    @0
    cZ
    csn
    #
    wceq
    #
    cX
    cZ
    wceq
    #
    wph
    @1
    @2
    @0
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @1
    @2
    wceq
    dih0vb.k
    cU
    cH
    cI
    cK
    cZ
    cW
    c.0
    dih0vb.o
    dih0vb.h
    dih0vb.i
    dih0vb.u
    dih0vb.z
    dih0
    syl
    eqeq2d
    wph
    cU
    clmod
    wcel
    cX
    cV
    wcel
    @3
    @4
    wb
    wph
    cU
    cH
    cK
    cW
    dih0vb.h
    dih0vb.u
    dih0vb.k
    dvhlmod
    dih0vb.x
    cN
    cV
    cU
    cX
    cZ
    dih0vb.v
    dih0vb.z
    dih0vb.n
    lspsneq0
    syl2anc
    bitr2d
end
