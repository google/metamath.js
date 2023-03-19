include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "chlt.mm"
include "cbs.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "lkrssv.mm"
include "dochocss.mm"
include "syl2anc.mm"
include "adantr.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "wne.mm"
include "clmod.mm"
include "simpr.mm"
include "lshpne.mm"
include "ex.mm"
include "wn.mm"
include "lkrshpor.mm"
include "ord.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "adantl.mm"
include "dochoc1.mm"
include "eqtrd.mm"
include "syld.mm"
include "necon1ad.mm"
include "imp.mm"
include "lshpcmp.mm"
include "mpbid.mm"
include "eqcomd.mm"
include "jca.mm"
include "eleq1.mm"
include "biimpar.mm"
include "impbid1.mm"

theorem dochlkr
  let wph: wff ph
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  let cY: class Y
  assume dochlkr.h: |- H = ( LHyp ` K )
  assume dochlkr.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochlkr.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochlkr.f: |- F = ( LFnl ` U )
  assume dochlkr.y: |- Y = ( LSHyp ` U )
  assume dochlkr.l: |- L = ( LKer ` U )
  assume dochlkr.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochlkr.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) e. Y <-> ( ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) = ( L ` G ) /\ ( L ` G ) e. Y ) ) )

  proof
    wph
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cY
    wcel
    #
    @2
    @0
    wceq
    #
    @0
    cY
    wcel
    #
    wa
    #
    wph
    @3
    @6
    wph
    @3
    wa
    #
    @4
    @5
    @7
    @0
    @2
    @7
    @0
    @2
    wss
    #
    @0
    @2
    wceq
    wph
    @8
    @3
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
    cU
    cbs
    cfv
    #
    wss
    @8
    dochlkr.k
    wph
    cF
    cG
    cL
    @10
    cU
    @10
    eqid
    #
    dochlkr.f
    dochlkr.l
    wph
    cU
    cH
    cK
    cW
    dochlkr.h
    dochlkr.u
    dochlkr.k
    dvhlmod
    #
    dochlkr.g
    lkrssv
    cU
    cH
    cK
    c.pe
    @10
    cW
    @0
    dochlkr.h
    dochlkr.u
    @11
    dochlkr.o
    dochocss
    syl2anc
    adantr
    @7
    @0
    @2
    cY
    cU
    dochlkr.y
    wph
    cU
    clvec
    wcel
    @3
    wph
    cU
    cH
    cK
    cW
    dochlkr.h
    dochlkr.u
    dochlkr.k
    dvhlvec
    #
    adantr
    wph
    @3
    @5
    wph
    @3
    @2
    @10
    wne
    #
    @5
    wph
    @3
    @14
    @7
    @2
    cY
    @10
    cU
    @11
    dochlkr.y
    wph
    cU
    clmod
    wcel
    @3
    @12
    adantr
    wph
    @3
    simpr
    #
    lshpne
    ex
    wph
    @5
    @2
    @10
    wph
    @5
    wn
    @0
    @10
    wceq
    #
    @2
    @10
    wceq
    #
    wph
    @5
    @16
    wph
    cF
    cG
    cY
    cL
    @10
    cU
    @11
    dochlkr.y
    dochlkr.f
    dochlkr.l
    @13
    dochlkr.g
    lkrshpor
    ord
    wph
    @16
    @17
    wph
    @16
    wa
    #
    @2
    @10
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @10
    @16
    @2
    @20
    wceq
    wph
    @16
    @1
    @19
    c.pe
    @0
    @10
    c.pe
    fveq2
    fveq2d
    adantl
    @18
    cU
    cH
    cK
    c.pe
    @10
    cW
    dochlkr.h
    dochlkr.u
    dochlkr.o
    @11
    wph
    @9
    @16
    dochlkr.k
    adantr
    dochoc1
    eqtrd
    ex
    syld
    necon1ad
    syld
    imp
    #
    @15
    lshpcmp
    mpbid
    eqcomd
    @21
    jca
    ex
    @4
    @3
    @5
    @2
    @0
    cY
    eleq1
    biimpar
    impbid1
end
