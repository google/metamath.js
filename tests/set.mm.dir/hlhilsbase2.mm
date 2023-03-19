include "cedring.mm"
include "cfv.mm"
include "cbs.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "eqid.mm"
include "dvhsca.mm"
include "syl.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "hlhilsbase.mm"
include "eqtrd.mm"

theorem hlhilsbase2
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cL: class L
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume hlhilsbase.h: |- H = ( LHyp ` K )
  assume hlhilsbase.l: |- L = ( ( DVecH ` K ) ` W )
  assume hlhilsbase.s: |- S = ( Scalar ` L )
  assume hlhilsbase.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhilsbase.r: |- R = ( Scalar ` U )
  assume hlhilsbase.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhilsbase2.c: |- C = ( Base ` S )


  assert |- ( ph -> C = ( Base ` R ) )

  proof
    wph
    cC
    cW
    cK
    cedring
    cfv
    cfv
    #
    cbs
    cfv
    #
    cR
    cbs
    cfv
    wph
    cC
    cS
    cbs
    cfv
    @1
    hlhilsbase2.c
    wph
    cS
    @0
    cbs
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cS
    @0
    wceq
    hlhilsbase.k
    @0
    cL
    cS
    cH
    cK
    cW
    chlt
    hlhilsbase.h
    @0
    eqid
    #
    hlhilsbase.l
    hlhilsbase.s
    dvhsca
    syl
    fveq2d
    syl5eq
    wph
    @1
    cR
    cU
    @0
    cH
    cK
    cW
    hlhilsbase.h
    @2
    hlhilsbase.u
    hlhilsbase.r
    hlhilsbase.k
    @1
    eqid
    hlhilsbase
    eqtrd
end
