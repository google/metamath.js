include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cbs.mm"
include "cfv.mm"
include "cres.mm"
include "crh.mm"
include "co.mm"
include "ccid.mm"
include "crg.mm"
include "cin.mm"
include "eleq2d.mm"
include "elin.mm"
include "simplbi.mm"
include "syl6bi.mm"
include "imp.mm"
include "eqid.mm"
include "idrhm.mm"
include "syl.mm"
include "adantr.mm"
include "simprbi.mm"
include "estrcid.mm"
include "cxp.mm"
include "cringc.mm"
include "chom.mm"
include "oveqdr.mm"
include "wceq.mm"
include "ringchomfval.mm"
include "ringcbas.mm"
include "incom.mm"
include "syl6eq.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "oveqd.mm"
include "biimpa.mm"
include "eleqtrrd.mm"
include "ringchom.mm"
include "3eqtrd.mm"
include "3eltr4d.mm"

theorem rhmsubcsetclem1
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let vk: setvar k
  assume rhmsubcsetc.c: |- C = ( ExtStrCat ` U )
  assume rhmsubcsetc.u: |- ( ph -> U e. V )
  assume rhmsubcsetc.b: |- ( ph -> B = ( Ring i^i U ) )
  assume rhmsubcsetc.h: |- ( ph -> H = ( RingHom |` ( B X. B ) ) )


  assert |- ( ( ph /\ x e. B ) -> ( ( Id ` C ) ` x ) e. ( x H x ) )

  proof
    wph
    vx
    cv
    #
    cB
    wcel
    #
    wa
    #
    cid
    @0
    cbs
    cfv
    #
    cres
    #
    @0
    @0
    crh
    co
    #
    @0
    cC
    ccid
    cfv
    #
    cfv
    @0
    @0
    cH
    co
    #
    @2
    @0
    crg
    wcel
    #
    @4
    @5
    wcel
    wph
    @1
    @8
    wph
    @1
    @0
    crg
    cU
    cin
    #
    wcel
    #
    @8
    wph
    cB
    @9
    @0
    rhmsubcsetc.b
    eleq2d
    #
    @10
    @8
    @0
    cU
    wcel
    #
    @0
    crg
    cU
    elin
    #
    simplbi
    syl6bi
    imp
    @3
    @0
    @3
    eqid
    idrhm
    syl
    @2
    cC
    cU
    @6
    cV
    @0
    rhmsubcsetc.c
    @6
    eqid
    wph
    cU
    cV
    wcel
    @1
    rhmsubcsetc.u
    adantr
    #
    wph
    @1
    @12
    wph
    @1
    @10
    @12
    @11
    @10
    @8
    @12
    @13
    simprbi
    syl6bi
    imp
    estrcid
    @2
    @7
    @0
    @0
    crh
    cB
    cB
    cxp
    #
    cres
    #
    co
    @0
    @0
    cU
    cringc
    cfv
    #
    chom
    cfv
    #
    co
    @5
    wph
    @1
    vx
    vx
    cH
    @16
    rhmsubcsetc.h
    oveqdr
    @2
    @16
    @18
    @0
    @0
    @2
    @18
    @16
    wph
    @18
    @16
    wceq
    @1
    wph
    @18
    crh
    @17
    cbs
    cfv
    #
    @19
    cxp
    #
    cres
    @16
    wph
    @19
    @17
    cU
    @18
    cV
    @17
    eqid
    #
    @19
    eqid
    #
    rhmsubcsetc.u
    @18
    eqid
    #
    ringchomfval
    wph
    @20
    @15
    crh
    wph
    @19
    cB
    wph
    @19
    cU
    crg
    cin
    #
    cB
    wph
    @19
    @17
    cU
    cV
    @21
    @22
    rhmsubcsetc.u
    ringcbas
    #
    wph
    cB
    @24
    wph
    cB
    @9
    @24
    rhmsubcsetc.b
    crg
    cU
    incom
    syl6eq
    #
    eqcomd
    eqtrd
    sqxpeqd
    reseq2d
    eqtrd
    adantr
    eqcomd
    oveqd
    @2
    @19
    @17
    cU
    @18
    cV
    @0
    @0
    @21
    @22
    @14
    @23
    @2
    @0
    @24
    @19
    wph
    @1
    @0
    @24
    wcel
    wph
    cB
    @24
    @0
    @26
    eleq2d
    biimpa
    wph
    @19
    @24
    wceq
    @1
    @25
    adantr
    eleqtrrd
    #
    @27
    ringchom
    3eqtrd
    3eltr4d
end
