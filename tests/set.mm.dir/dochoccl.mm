include "crn.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "chlt.mm"
include "wa.mm"
include "dochoc.mm"
include "sylan.mm"
include "simpr.mm"
include "wss.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "dochcl.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "impbida.mm"

theorem dochoccl
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  assume dochoccl.h: |- H = ( LHyp ` K )
  assume dochoccl.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dochoccl.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochoccl.v: |- V = ( Base ` U )
  assume dochoccl.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochoccl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochoccl.g: |- ( ph -> X C_ V )


  assert |- ( ph -> ( X e. ran I <-> ( ._|_ ` ( ._|_ ` X ) ) = X ) )

  proof
    wph
    cX
    cI
    crn
    #
    wcel
    #
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cX
    wceq
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
    @1
    @4
    dochoccl.k
    cH
    cI
    cK
    c.pe
    cW
    cX
    dochoccl.h
    dochoccl.i
    dochoccl.o
    dochoc
    sylan
    wph
    @4
    wa
    @3
    cX
    @0
    wph
    @4
    simpr
    wph
    @3
    @0
    wcel
    #
    @4
    wph
    @5
    @2
    cV
    wss
    #
    @6
    dochoccl.k
    wph
    @5
    cX
    cV
    wss
    @7
    dochoccl.k
    dochoccl.g
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    dochoccl.h
    dochoccl.u
    dochoccl.v
    dochoccl.o
    dochssv
    syl2anc
    cU
    cH
    cI
    cK
    c.pe
    cV
    cW
    @2
    dochoccl.h
    dochoccl.i
    dochoccl.u
    dochoccl.v
    dochoccl.o
    dochcl
    syl2anc
    adantr
    eqeltrrd
    impbida
end
