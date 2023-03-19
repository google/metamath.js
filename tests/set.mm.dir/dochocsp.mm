include "cfv.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lspssv.mm"
include "syl2anc.mm"
include "lspssid.mm"
include "dochss.mm"
include "syl3anc.mm"
include "cdih.mm"
include "crn.mm"
include "wceq.mm"
include "eqid.mm"
include "dochcl.mm"
include "dochoc.mm"
include "dochssv.mm"
include "dochspss.mm"
include "eqsstr3d.mm"
include "eqssd.mm"

theorem dochocsp
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


  assert |- ( ph -> ( ._|_ ` ( N ` X ) ) = ( ._|_ ` X ) )

  proof
    wph
    cX
    cN
    cfv
    #
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
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
    cV
    wss
    #
    cX
    @0
    wss
    #
    @1
    @2
    wss
    dochsp.k
    wph
    cU
    clmod
    wcel
    #
    cX
    cV
    wss
    #
    @4
    wph
    cU
    cH
    cK
    cW
    dochsp.h
    dochsp.u
    dochsp.k
    dvhlmod
    #
    dochsp.x
    cX
    cN
    cV
    cU
    dochsp.v
    dochsp.n
    lspssv
    syl2anc
    wph
    @6
    @7
    @5
    @8
    dochsp.x
    cX
    cN
    cV
    cU
    dochsp.v
    dochsp.n
    lspssid
    syl2anc
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    @0
    dochsp.h
    dochsp.u
    dochsp.v
    dochsp.o
    dochss
    syl3anc
    wph
    @2
    @2
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @1
    wph
    @3
    @2
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    wcel
    #
    @10
    @2
    wceq
    dochsp.k
    wph
    @3
    @7
    @12
    dochsp.k
    dochsp.x
    cU
    cH
    @11
    cK
    c.pe
    cV
    cW
    cX
    dochsp.h
    @11
    eqid
    #
    dochsp.u
    dochsp.v
    dochsp.o
    dochcl
    syl2anc
    cH
    @11
    cK
    c.pe
    cW
    @2
    dochsp.h
    @13
    dochsp.o
    dochoc
    syl2anc
    wph
    @3
    @9
    cV
    wss
    #
    @0
    @9
    wss
    @10
    @1
    wss
    dochsp.k
    wph
    @3
    @2
    cV
    wss
    #
    @14
    dochsp.k
    wph
    @3
    @7
    @15
    dochsp.k
    dochsp.x
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
    dochsp.o
    dochssv
    syl2anc
    cU
    cH
    cK
    c.pe
    cV
    cW
    @2
    dochsp.h
    dochsp.u
    dochsp.v
    dochsp.o
    dochssv
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
    dochspss
    cU
    cH
    cK
    c.pe
    cV
    cW
    @0
    @9
    dochsp.h
    dochsp.u
    dochsp.v
    dochsp.o
    dochss
    syl3anc
    eqsstr3d
    eqssd
end
