include "cnx.mm"
include "cstv.mm"
include "cfv.mm"
include "chg.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "ndxid.mm"
include "wne.mm"
include "c4.mm"
include "nnrei.mm"
include "ltneii.mm"
include "ndxarg.mm"
include "starvndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "eqtri.mm"
include "csca.mm"
include "eqid.mm"
include "hlhilsca.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "syl5eq.mm"

theorem hlhilslem
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cN: class N
  let cW: class W
  assume hlhilslem.h: |- H = ( LHyp ` K )
  assume hlhilslem.e: |- E = ( ( EDRing ` K ) ` W )
  assume hlhilslem.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhilslem.r: |- R = ( Scalar ` U )
  assume hlhilslem.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhilslem.f: |- F = Slot N
  assume hlhilslem.1: |- N e. NN
  assume hlhilslem.2: |- N < 4
  assume hlhilslem.c: |- C = ( F ` E )


  assert |- ( ph -> C = ( F ` R ) )

  proof
    wph
    cC
    cE
    cnx
    cstv
    cfv
    #
    cW
    cK
    chg
    cfv
    cfv
    #
    cop
    csts
    co
    #
    cF
    cfv
    #
    cR
    cF
    cfv
    cC
    cE
    cF
    cfv
    @3
    hlhilslem.c
    @1
    @0
    cF
    cE
    cF
    cN
    hlhilslem.f
    hlhilslem.1
    ndxid
    cnx
    cF
    cfv
    #
    @0
    wne
    cN
    c4
    wne
    cN
    c4
    cN
    hlhilslem.1
    nnrei
    hlhilslem.2
    ltneii
    @4
    cN
    @0
    c4
    cF
    cN
    hlhilslem.f
    hlhilslem.1
    ndxarg
    starvndx
    neeq12i
    mpbir
    setsnid
    eqtri
    wph
    @2
    cR
    cF
    wph
    @2
    cU
    csca
    cfv
    cR
    wph
    @2
    cU
    cE
    @1
    cH
    cK
    cW
    hlhilslem.h
    hlhilslem.u
    hlhilslem.k
    hlhilslem.e
    @1
    eqid
    @2
    eqid
    hlhilsca
    hlhilslem.r
    syl6eqr
    fveq2d
    syl5eq
end
