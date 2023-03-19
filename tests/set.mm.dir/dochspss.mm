include "cv.mm"
include "wss.mm"
include "clss.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "cdih.mm"
include "crn.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "eqid.mm"
include "dihsslss.mm"
include "rabss2.mm"
include "intss.mm"
include "4syl.mm"
include "clmod.mm"
include "wceq.mm"
include "dvhlmod.mm"
include "lspval.mm"
include "syl2anc.mm"
include "doch2val2.mm"
include "3sstr4d.mm"

theorem dochspss
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


  assert |- ( ph -> ( N ` X ) C_ ( ._|_ ` ( ._|_ ` X ) ) )

  proof
    wph
    cX
    vz
    cv
    wss
    #
    vz
    cU
    clss
    cfv
    #
    crab
    #
    cint
    #
    @0
    vz
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    #
    crab
    #
    cint
    #
    cX
    cN
    cfv
    #
    cX
    c.pe
    cfv
    c.pe
    cfv
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @5
    @1
    wss
    @6
    @2
    wss
    @3
    @7
    wss
    dochsp.k
    @1
    cU
    cH
    @4
    cK
    cW
    dochsp.h
    dochsp.u
    @4
    eqid
    #
    @1
    eqid
    #
    dihsslss
    @0
    vz
    @5
    @1
    rabss2
    @6
    @2
    intss
    4syl
    wph
    cU
    clmod
    wcel
    cX
    cV
    wss
    @8
    @3
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
    dochsp.x
    vz
    @1
    cX
    cN
    cV
    cU
    dochsp.v
    @10
    dochsp.n
    lspval
    syl2anc
    wph
    vz
    cU
    cH
    @4
    cK
    c.pe
    cV
    cW
    cX
    dochsp.h
    @9
    dochsp.u
    dochsp.v
    dochsp.o
    dochsp.k
    dochsp.x
    doch2val2
    3sstr4d
end
