include "clsa.mm"
include "cfv.mm"
include "clss.mm"
include "clsh.mm"
include "cbs.mm"
include "cvv.mm"
include "c0g.mm"
include "eqid.mm"
include "wcel.mm"
include "cdvh.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cpw.mm"
include "cdih.mm"
include "crn.mm"
include "dochfN.mm"
include "chlt.mm"
include "wa.mm"
include "wss.mm"
include "dihsslss.mm"
include "syl.mm"
include "fssd.mm"
include "csn.mm"
include "wceq.mm"
include "doch1.mm"
include "cv.mm"
include "w3a.mm"
include "adantr.mm"
include "simpr2.mm"
include "simpr3.mm"
include "dochss.mm"
include "syl3anc.mm"
include "simpr.mm"
include "dochsatshp.mm"
include "dih1dimat.mm"
include "syl2anc.mm"
include "dochoc.mm"
include "islpoldN.mm"

theorem dochpolN
  let wph: wff ph
  let cP: class P
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume dochpol.h: |- H = ( LHyp ` K )
  assume dochpol.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochpol.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochpol.p: |- P = ( LPol ` U )
  assume dochpol.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> ._|_ e. P )

  proof
    wph
    vx
    vy
    cU
    clsa
    cfv
    #
    cP
    cU
    clss
    cfv
    #
    cU
    clsh
    cfv
    #
    c.pe
    cU
    cbs
    cfv
    #
    cU
    cvv
    cU
    c0g
    cfv
    #
    @3
    eqid
    #
    @1
    eqid
    #
    @4
    eqid
    #
    @0
    eqid
    #
    @2
    eqid
    #
    dochpol.p
    cU
    cvv
    wcel
    wph
    cU
    cW
    cK
    cdvh
    cfv
    #
    cfv
    cvv
    dochpol.u
    cW
    @10
    fvex
    eqeltri
    a1i
    wph
    @3
    cpw
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    #
    @1
    c.pe
    wph
    cU
    cH
    @11
    cK
    c.pe
    @3
    cW
    dochpol.h
    @11
    eqid
    #
    dochpol.u
    @5
    dochpol.o
    dochpol.k
    dochfN
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @12
    @1
    wss
    dochpol.k
    @1
    cU
    cH
    @11
    cK
    cW
    dochpol.h
    dochpol.u
    @13
    @6
    dihsslss
    syl
    fssd
    wph
    @14
    @3
    c.pe
    cfv
    @4
    csn
    wceq
    dochpol.k
    cU
    cH
    cK
    c.pe
    @3
    cW
    @4
    dochpol.h
    dochpol.u
    dochpol.o
    @5
    @7
    doch1
    syl
    wph
    vx
    cv
    #
    @3
    wss
    #
    vy
    cv
    #
    @3
    wss
    #
    @15
    @17
    wss
    #
    w3a
    #
    wa
    @14
    @18
    @19
    @17
    c.pe
    cfv
    @15
    c.pe
    cfv
    #
    wss
    wph
    @14
    @20
    dochpol.k
    adantr
    wph
    @16
    @18
    @19
    simpr2
    wph
    @16
    @18
    @19
    simpr3
    cU
    cH
    cK
    c.pe
    @3
    cW
    @15
    @17
    dochpol.h
    dochpol.u
    @5
    dochpol.o
    dochss
    syl3anc
    wph
    @15
    @0
    wcel
    #
    wa
    #
    @0
    @15
    cU
    cH
    cK
    c.pe
    cW
    @2
    dochpol.h
    dochpol.u
    dochpol.o
    @8
    @9
    wph
    @14
    @22
    dochpol.k
    adantr
    #
    wph
    @22
    simpr
    #
    dochsatshp
    @23
    @14
    @15
    @12
    wcel
    #
    @21
    c.pe
    cfv
    @15
    wceq
    @24
    @23
    @14
    @22
    @26
    @24
    @25
    @0
    @15
    cU
    cH
    @11
    cK
    cW
    dochpol.h
    dochpol.u
    @13
    @8
    dih1dimat
    syl2anc
    cH
    @11
    cK
    c.pe
    cW
    @15
    dochpol.h
    @13
    dochpol.o
    dochoc
    syl2anc
    islpoldN
end
