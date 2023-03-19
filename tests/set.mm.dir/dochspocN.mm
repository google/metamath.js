include "cfv.mm"
include "clmod.mm"
include "wcel.mm"
include "clss.mm"
include "wceq.mm"
include "dvhlmod.mm"
include "chlt.mm"
include "wa.mm"
include "wss.mm"
include "eqid.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "lspid.mm"
include "dochocsp.mm"
include "eqtr4d.mm"

theorem dochspocN
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let vz: setvar z
  assume dochsp.h: |- H = ( LHyp ` K )
  assume dochsp.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochsp.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochsp.v: |- V = ( Base ` U )
  assume dochsp.n: |- N = ( LSpan ` U )
  assume dochsp.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochsp.x: |- ( ph -> X C_ V )


  assert |- ( ph -> ( N ` ( ._|_ ` X ) ) = ( ._|_ ` ( N ` X ) ) )

  proof
    wph
    cX
    c.pe
    cfv
    #
    cN
    cfv
    #
    @0
    cX
    cN
    cfv
    c.pe
    cfv
    wph
    cU
    clmod
    wcel
    @0
    cU
    clss
    cfv
    #
    wcel
    #
    @1
    @0
    wceq
    wph
    cU
    cH
    cK
    cW
    dochsp.h
    dochsp.u
    dochsp.k
    dvhlmod
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cX
    cV
    wss
    @3
    dochsp.k
    dochsp.x
    @2
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    dochsp.h
    dochsp.u
    dochsp.v
    @2
    eqid
    #
    dochsp.o
    dochlss
    syl2anc
    @2
    @0
    cN
    cU
    @4
    dochsp.n
    lspid
    syl2anc
    wph
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    cX
    dochsp.h
    dochsp.u
    dochsp.o
    dochsp.v
    dochsp.n
    dochsp.k
    dochsp.x
    dochocsp
    eqtr4d
end
