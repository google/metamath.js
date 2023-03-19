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
include "crng.mm"
include "ringrng.mm"
include "anim2i.mm"
include "ancoms.mm"
include "sylbi.mm"
include "adantl.mm"
include "sylibr.mm"
include "wceq.mm"
include "rngcbas.mm"
include "eleqtrrd.mm"
include "ex.mm"
include "sylbid.mm"
include "rngcid.mm"
include "cxp.mm"
include "cringc.mm"
include "chom.mm"
include "oveqdr.mm"
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
include "ringchom.mm"
include "3eqtrd.mm"
include "3eltr4d.mm"

theorem rhmsubcrngclem1
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let vk: setvar k
  assume rhmsubcrngc.c: |- C = ( RngCat ` U )
  assume rhmsubcrngc.u: |- ( ph -> U e. V )
  assume rhmsubcrngc.b: |- ( ph -> B = ( Ring i^i U ) )
  assume rhmsubcrngc.h: |- ( ph -> H = ( RingHom |` ( B X. B ) ) )


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
    rhmsubcrngc.b
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
    #
    idrhm
    syl
    @2
    cC
    cbs
    cfv
    #
    cC
    @3
    cU
    @6
    cV
    @0
    rhmsubcrngc.c
    @15
    eqid
    #
    @6
    eqid
    wph
    cU
    cV
    wcel
    @1
    rhmsubcrngc.u
    adantr
    #
    wph
    @1
    @0
    @15
    wcel
    #
    wph
    @1
    @10
    @18
    @11
    wph
    @10
    @18
    wph
    @10
    wa
    #
    @0
    cU
    crng
    cin
    #
    @15
    @19
    @12
    @0
    crng
    wcel
    #
    wa
    #
    @0
    @20
    wcel
    @10
    @22
    wph
    @10
    @8
    @12
    wa
    @22
    @13
    @12
    @8
    @22
    @8
    @21
    @12
    @0
    ringrng
    anim2i
    ancoms
    sylbi
    adantl
    @0
    cU
    crng
    elin
    sylibr
    wph
    @15
    @20
    wceq
    @10
    wph
    @15
    cC
    cU
    cV
    rhmsubcrngc.c
    @16
    rhmsubcrngc.u
    rngcbas
    adantr
    eleqtrrd
    ex
    sylbid
    imp
    @14
    rngcid
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
    @24
    rhmsubcrngc.h
    oveqdr
    @2
    @24
    @26
    @0
    @0
    @2
    @26
    @24
    wph
    @26
    @24
    wceq
    @1
    wph
    @26
    crh
    @25
    cbs
    cfv
    #
    @27
    cxp
    #
    cres
    @24
    wph
    @27
    @25
    cU
    @26
    cV
    @25
    eqid
    #
    @27
    eqid
    #
    rhmsubcrngc.u
    @26
    eqid
    #
    ringchomfval
    wph
    @28
    @23
    crh
    wph
    @27
    cB
    wph
    @27
    cU
    crg
    cin
    #
    cB
    wph
    @27
    @25
    cU
    cV
    @29
    @30
    rhmsubcrngc.u
    ringcbas
    #
    wph
    cB
    @32
    wph
    cB
    @9
    @32
    rhmsubcrngc.b
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
    @27
    @25
    cU
    @26
    cV
    @0
    @0
    @29
    @30
    @17
    @31
    @2
    @0
    @32
    @27
    wph
    @1
    @0
    @32
    wcel
    wph
    cB
    @32
    @0
    @34
    eleq2d
    biimpa
    wph
    @27
    @32
    wceq
    @1
    @33
    adantr
    eleqtrrd
    #
    @35
    ringchom
    3eqtrd
    3eltr4d
end
