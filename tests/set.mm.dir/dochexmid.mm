include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "c0g.mm"
include "csn.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "csubg.mm"
include "wcel.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "chlt.mm"
include "wa.mm"
include "wss.mm"
include "eqid.mm"
include "lmod0vcl.mm"
include "syl.mm"
include "snssd.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "lsssubg.mm"
include "lsm02.mm"
include "doch0.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "wne.mm"
include "clsa.mm"
include "clspn.mm"
include "adantr.mm"
include "simpr.mm"
include "dochexmidlem8.mm"
include "pm2.61dane.mm"

theorem dochexmid
  let wph: wff ph
  let c.po: class .(+)
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  assume dochexmid.h: |- H = ( LHyp ` K )
  assume dochexmid.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochexmid.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochexmid.v: |- V = ( Base ` U )
  assume dochexmid.s: |- S = ( LSubSp ` U )
  assume dochexmid.p: |- .(+) = ( LSSum ` U )
  assume dochexmid.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochexmid.x: |- ( ph -> X e. S )
  assume dochexmid.c: |- ( ph -> ( ._|_ ` ( ._|_ ` X ) ) = X )


  assert |- ( ph -> ( X .(+) ( ._|_ ` X ) ) = V )

  proof
    wph
    cX
    cX
    c.pe
    cfv
    #
    c.po
    co
    #
    cV
    wceq
    cX
    cU
    c0g
    cfv
    #
    csn
    #
    cX
    @3
    wceq
    #
    wph
    @1
    @3
    @3
    c.pe
    cfv
    #
    c.po
    co
    #
    cV
    @4
    cX
    @3
    @0
    @5
    c.po
    @4
    id
    cX
    @3
    c.pe
    fveq2
    oveq12d
    wph
    @6
    @5
    cV
    wph
    @5
    cU
    csubg
    cfv
    wcel
    #
    @6
    @5
    wceq
    wph
    cU
    clmod
    wcel
    #
    @5
    cS
    wcel
    #
    @7
    wph
    cU
    cH
    cK
    cW
    dochexmid.h
    dochexmid.u
    dochexmid.k
    dvhlmod
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
    @3
    cV
    wss
    @9
    dochexmid.k
    wph
    @2
    cV
    wph
    @8
    @2
    cV
    wcel
    @10
    cV
    cU
    @2
    dochexmid.v
    @2
    eqid
    #
    lmod0vcl
    syl
    snssd
    cS
    cU
    cH
    cK
    c.pe
    cV
    cW
    @3
    dochexmid.h
    dochexmid.u
    dochexmid.v
    dochexmid.s
    dochexmid.o
    dochlss
    syl2anc
    cS
    @5
    cU
    dochexmid.s
    lsssubg
    syl2anc
    c.po
    cU
    @5
    @2
    @12
    dochexmid.p
    lsm02
    syl
    wph
    @11
    @5
    cV
    wceq
    dochexmid.k
    cU
    cH
    cK
    c.pe
    cV
    cW
    @2
    dochexmid.h
    dochexmid.u
    dochexmid.o
    dochexmid.v
    @12
    doch0
    syl
    eqtrd
    sylan9eqr
    wph
    cX
    @3
    wne
    #
    wa
    cU
    clsa
    cfv
    #
    c.po
    cS
    cU
    cH
    cK
    cU
    clspn
    cfv
    #
    c.pe
    cV
    cW
    cX
    @2
    dochexmid.h
    dochexmid.o
    dochexmid.u
    dochexmid.v
    dochexmid.s
    @15
    eqid
    dochexmid.p
    @14
    eqid
    wph
    @11
    @13
    dochexmid.k
    adantr
    wph
    cX
    cS
    wcel
    @13
    dochexmid.x
    adantr
    @12
    wph
    @13
    simpr
    wph
    @0
    c.pe
    cfv
    cX
    wceq
    @13
    dochexmid.c
    adantr
    dochexmidlem8
    pm2.61dane
end
