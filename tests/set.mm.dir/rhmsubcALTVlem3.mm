include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cbs.mm"
include "cfv.mm"
include "cres.mm"
include "crh.mm"
include "co.mm"
include "crngcALTV.mm"
include "ccid.mm"
include "crg.mm"
include "cin.mm"
include "eleq2d.mm"
include "elinel1.mm"
include "syl6bi.mm"
include "imp.mm"
include "eqid.mm"
include "idrhm.mm"
include "syl.mm"
include "cvv.mm"
include "ccat.mm"
include "cmpt.mm"
include "wceq.mm"
include "adantr.mm"
include "rngccatidALTV.mm"
include "simpr.mm"
include "3syl.mm"
include "weq.mm"
include "fveq2.mm"
include "reseq2d.mm"
include "adantl.mm"
include "crng.mm"
include "incom.mm"
include "syl6eq.mm"
include "ringrng.mm"
include "anim2i.mm"
include "elin.mm"
include "3imtr4i.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "rngcbasALTV.mm"
include "eleqtrrd.mm"
include "fvexd.mm"
include "resiexd.mm"
include "fvmptd.mm"
include "rhmsubcALTVlem2.mm"
include "3anidm23.mm"
include "3eltr4d.mm"

theorem rhmsubcALTVlem3
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cR: class R
  let cU: class U
  let cH: class H
  let cV: class V
  let vy: setvar y
  let vk: setvar k
  assume rngcrescrhmALTV.u: |- ( ph -> U e. V )
  assume rngcrescrhmALTV.c: |- C = ( RngCatALTV ` U )
  assume rngcrescrhmALTV.r: |- ( ph -> R = ( Ring i^i U ) )
  assume rngcrescrhmALTV.h: |- H = ( RingHom |` ( R X. R ) )

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint U y
  disjoint V y
  disjoint ph y
  disjoint k x
  assert |- ( ( ph /\ x e. R ) -> ( ( Id ` ( RngCatALTV ` U ) ) ` x ) e. ( x H x ) )

  proof
    wph
    vx
    cv
    #
    cR
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
    cU
    crngcALTV
    cfv
    #
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
    @9
    wph
    @1
    @0
    crg
    cU
    cin
    #
    wcel
    @9
    wph
    cR
    @10
    @0
    rngcrescrhmALTV.r
    eleq2d
    @0
    crg
    cU
    elinel1
    syl6bi
    imp
    @3
    @0
    @3
    eqid
    idrhm
    syl
    @2
    vy
    @0
    cid
    vy
    cv
    #
    cbs
    cfv
    #
    cres
    #
    @4
    @6
    cbs
    cfv
    #
    @7
    cvv
    @2
    cU
    cV
    wcel
    #
    @6
    ccat
    wcel
    #
    @7
    vy
    @14
    @13
    cmpt
    wceq
    #
    wa
    @17
    wph
    @15
    @1
    rngcrescrhmALTV.u
    adantr
    vy
    @14
    @6
    cU
    cV
    @6
    eqid
    @14
    eqid
    rngccatidALTV
    @16
    @17
    simpr
    3syl
    vy
    vx
    weq
    #
    @13
    @4
    wceq
    @2
    @18
    @12
    @3
    cid
    @11
    @0
    cbs
    fveq2
    reseq2d
    adantl
    @2
    @0
    cU
    crng
    cin
    #
    @14
    wph
    @1
    @0
    @19
    wcel
    #
    wph
    @1
    @0
    cU
    crg
    cin
    #
    wcel
    #
    @20
    wph
    cR
    @21
    @0
    wph
    cR
    @10
    @21
    rngcrescrhmALTV.r
    crg
    cU
    incom
    syl6eq
    eleq2d
    @0
    cU
    wcel
    #
    @9
    wa
    @23
    @0
    crng
    wcel
    #
    wa
    @22
    @20
    @9
    @24
    @23
    @0
    ringrng
    anim2i
    @0
    cU
    crg
    elin
    @0
    cU
    crng
    elin
    3imtr4i
    syl6bi
    imp
    wph
    @14
    @19
    wceq
    @1
    wph
    @14
    cC
    cU
    cV
    rngcrescrhmALTV.c
    @6
    cC
    cbs
    cC
    @6
    rngcrescrhmALTV.c
    eqcomi
    fveq2i
    rngcrescrhmALTV.u
    rngcbasALTV
    adantr
    eleqtrrd
    @2
    @3
    cvv
    @2
    @0
    cbs
    fvexd
    resiexd
    fvmptd
    wph
    @1
    @8
    @5
    wceq
    wph
    cC
    cR
    cU
    cH
    cV
    @0
    @0
    rngcrescrhmALTV.u
    rngcrescrhmALTV.c
    rngcrescrhmALTV.r
    rngcrescrhmALTV.h
    rhmsubcALTVlem2
    3anidm23
    3eltr4d
end
