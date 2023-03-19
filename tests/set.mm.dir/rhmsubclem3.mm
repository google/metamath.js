include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cbs.mm"
include "cfv.mm"
include "cres.mm"
include "crh.mm"
include "co.mm"
include "crngc.mm"
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
include "eqcomi.mm"
include "fveq2i.mm"
include "adantr.mm"
include "crng.mm"
include "incom.mm"
include "wss.mm"
include "ringssrng.mm"
include "sslin.mm"
include "mp1i.mm"
include "syl5eqss.mm"
include "rngcbas.mm"
include "3sstr4d.mm"
include "sselda.mm"
include "rngcid.mm"
include "wceq.mm"
include "rhmsubclem2.mm"
include "3anidm23.mm"
include "3eltr4d.mm"

theorem rhmsubclem3
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cR: class R
  let cU: class U
  let cH: class H
  let cV: class V
  let vy: setvar y
  let vk: setvar k
  assume rngcrescrhm.u: |- ( ph -> U e. V )
  assume rngcrescrhm.c: |- C = ( RngCat ` U )
  assume rngcrescrhm.r: |- ( ph -> R = ( Ring i^i U ) )
  assume rngcrescrhm.h: |- H = ( RingHom |` ( R X. R ) )

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint C y
  disjoint U y
  disjoint V y
  disjoint ph y
  disjoint k x
  assert |- ( ( ph /\ x e. R ) -> ( ( Id ` ( RngCat ` U ) ) ` x ) e. ( x H x ) )

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
    crngc
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
    rngcrescrhm.r
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
    @7
    cV
    @0
    rngcrescrhm.c
    @12
    eqid
    #
    @6
    cC
    ccid
    cC
    @6
    rngcrescrhm.c
    eqcomi
    fveq2i
    wph
    cU
    cV
    wcel
    @1
    rngcrescrhm.u
    adantr
    wph
    cR
    @12
    @0
    wph
    @10
    cU
    crng
    cin
    #
    cR
    @12
    wph
    @10
    cU
    crg
    cin
    #
    @14
    crg
    cU
    incom
    crg
    crng
    wss
    @15
    @14
    wss
    wph
    ringssrng
    crg
    crng
    cU
    sslin
    mp1i
    syl5eqss
    rngcrescrhm.r
    wph
    @12
    cC
    cU
    cV
    rngcrescrhm.c
    @13
    rngcrescrhm.u
    rngcbas
    3sstr4d
    sselda
    @11
    rngcid
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
    rngcrescrhm.u
    rngcrescrhm.c
    rngcrescrhm.r
    rngcrescrhm.h
    rhmsubclem2
    3anidm23
    3eltr4d
end
