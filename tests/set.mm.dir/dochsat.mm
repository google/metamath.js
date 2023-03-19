include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "c0g.mm"
include "csn.mm"
include "clsm.mm"
include "co.mm"
include "wpss.mm"
include "wss.mm"
include "wceq.mm"
include "wne.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "adantr.mm"
include "eqid.mm"
include "lss0ss.mm"
include "syl2anc.mm"
include "simpr.mm"
include "lsatn0.mm"
include "fveq2d.mm"
include "dochoc0.mm"
include "eqtrd.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"
include "necomd.mm"
include "df-pss.mm"
include "sylanbrc.mm"
include "chlt.mm"
include "cbs.mm"
include "lssss.mm"
include "syl.mm"
include "dochocss.mm"
include "csubg.mm"
include "lsatlssel.mm"
include "lsssubg.mm"
include "lsm02.mm"
include "sseqtr4d.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lsssn0.mm"
include "lsmsatcv.mm"
include "mpd3an23.mm"
include "eqtr2d.mm"
include "eqeltrrd.mm"
include "cdih.mm"
include "crn.mm"
include "dih1dimat.mm"
include "sylan.mm"
include "dochoc.mm"
include "eqeltrd.mm"
include "impbida.mm"

theorem dochsat
  let wph: wff ph
  let cA: class A
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  assume dochsat.h: |- H = ( LHyp ` K )
  assume dochsat.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochsat.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochsat.s: |- S = ( LSubSp ` U )
  assume dochsat.a: |- A = ( LSAtoms ` U )
  assume dochsat.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochsat.q: |- ( ph -> Q e. S )


  assert |- ( ph -> ( ( ._|_ ` ( ._|_ ` Q ) ) e. A <-> Q e. A ) )

  proof
    wph
    cQ
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    wph
    @2
    wa
    #
    @1
    cQ
    cA
    @4
    cQ
    cU
    c0g
    cfv
    #
    csn
    #
    @1
    cU
    clsm
    cfv
    #
    co
    #
    @1
    @4
    @6
    cQ
    wpss
    #
    cQ
    @8
    wss
    cQ
    @8
    wceq
    @4
    @6
    cQ
    wss
    #
    @6
    cQ
    wne
    @9
    @4
    cU
    clmod
    wcel
    #
    cQ
    cS
    wcel
    #
    @10
    wph
    @11
    @2
    wph
    cU
    cH
    cK
    cW
    dochsat.h
    dochsat.u
    dochsat.k
    dvhlmod
    adantr
    #
    wph
    @12
    @2
    dochsat.q
    adantr
    #
    cS
    cU
    cQ
    @5
    @5
    eqid
    #
    dochsat.s
    lss0ss
    syl2anc
    @4
    cQ
    @6
    @4
    @1
    @6
    wne
    cQ
    @6
    wne
    @4
    cA
    @1
    cU
    @5
    @15
    dochsat.a
    @13
    wph
    @2
    simpr
    #
    lsatn0
    @4
    cQ
    @6
    @1
    @6
    @4
    cQ
    @6
    wceq
    #
    @1
    @6
    wceq
    @4
    @17
    wa
    #
    @1
    @6
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @6
    @18
    @0
    @19
    c.pe
    @18
    cQ
    @6
    c.pe
    @4
    @17
    simpr
    fveq2d
    fveq2d
    @4
    @20
    @6
    wceq
    #
    @17
    wph
    @21
    @2
    wph
    cU
    cH
    cK
    c.pe
    cW
    @5
    dochsat.h
    dochsat.u
    dochsat.o
    @15
    dochsat.k
    dochoc0
    adantr
    adantr
    eqtrd
    ex
    necon3d
    mpd
    necomd
    @6
    cQ
    df-pss
    sylanbrc
    @4
    cQ
    @1
    @8
    @4
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cQ
    cU
    cbs
    cfv
    #
    wss
    #
    cQ
    @1
    wss
    wph
    @22
    @2
    dochsat.k
    adantr
    wph
    @24
    @2
    wph
    @12
    @24
    dochsat.q
    cS
    cQ
    @23
    cU
    @23
    eqid
    #
    dochsat.s
    lssss
    syl
    adantr
    cU
    cH
    cK
    c.pe
    @23
    cW
    cQ
    dochsat.h
    dochsat.u
    @25
    dochsat.o
    dochocss
    syl2anc
    @4
    @1
    cU
    csubg
    cfv
    wcel
    #
    @8
    @1
    wceq
    @4
    @11
    @1
    cS
    wcel
    @26
    @13
    @4
    cA
    cS
    @1
    cU
    dochsat.s
    dochsat.a
    @13
    @16
    lsatlssel
    cS
    @1
    cU
    dochsat.s
    lsssubg
    syl2anc
    @7
    cU
    @1
    @5
    @15
    @7
    eqid
    #
    lsm02
    syl
    #
    sseqtr4d
    @4
    cA
    @7
    @1
    cS
    @6
    cQ
    cU
    dochsat.s
    @27
    dochsat.a
    wph
    cU
    clvec
    wcel
    @2
    wph
    cU
    cH
    cK
    cW
    dochsat.h
    dochsat.u
    dochsat.k
    dvhlvec
    adantr
    @4
    @11
    @6
    cS
    wcel
    @13
    cS
    cU
    @5
    @15
    dochsat.s
    lsssn0
    syl
    @14
    @16
    lsmsatcv
    mpd3an23
    @28
    eqtr2d
    @16
    eqeltrrd
    wph
    @3
    wa
    #
    @1
    cQ
    cA
    @29
    @22
    cQ
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    wcel
    #
    @1
    cQ
    wceq
    wph
    @22
    @3
    dochsat.k
    adantr
    wph
    @22
    @3
    @31
    dochsat.k
    cA
    cQ
    cU
    cH
    @30
    cK
    cW
    dochsat.h
    dochsat.u
    @30
    eqid
    #
    dochsat.a
    dih1dimat
    sylan
    cH
    @30
    cK
    c.pe
    cW
    cQ
    dochsat.h
    @32
    dochsat.o
    dochoc
    syl2anc
    wph
    @3
    simpr
    eqeltrd
    impbida
end
