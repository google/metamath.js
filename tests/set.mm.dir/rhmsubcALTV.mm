include "crngcALTV.mm"
include "cfv.mm"
include "csubc.mm"
include "wcel.mm"
include "chomf.mm"
include "cssc.mm"
include "wbr.mm"
include "cv.mm"
include "ccid.mm"
include "co.mm"
include "cop.mm"
include "cco.mm"
include "wral.mm"
include "wa.mm"
include "crh.mm"
include "cxp.mm"
include "cres.mm"
include "crngh.mm"
include "crng.mm"
include "cin.mm"
include "eqidd.mm"
include "rhmsscrnghm.mm"
include "wceq.mm"
include "a1i.mm"
include "eqid.mm"
include "rngchomrnghmresALTV.mm"
include "3brtr4d.mm"
include "rhmsubcALTVlem3.mm"
include "rhmsubcALTVlem4.mm"
include "ralrimivva.mm"
include "jca.mm"
include "ralrimiva.mm"
include "ccat.mm"
include "rngccatALTV.mm"
include "syl.mm"
include "rhmsubcALTVlem1.mm"
include "issubc2.mm"
include "mpbir2and.mm"

theorem rhmsubcALTV
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cU: class U
  let cH: class H
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  assume rngcrescrhmALTV.u: |- ( ph -> U e. V )
  assume rngcrescrhmALTV.c: |- C = ( RngCatALTV ` U )
  assume rngcrescrhmALTV.r: |- ( ph -> R = ( Ring i^i U ) )
  assume rngcrescrhmALTV.h: |- H = ( RingHom |` ( R X. R ) )


  assert |- ( ph -> H e. ( Subcat ` ( RngCatALTV ` U ) ) )

  proof
    wph
    cH
    cU
    crngcALTV
    cfv
    #
    csubc
    cfv
    wcel
    cH
    @0
    chomf
    cfv
    #
    cssc
    wbr
    vx
    cv
    #
    @0
    ccid
    cfv
    #
    cfv
    @2
    @2
    cH
    co
    wcel
    #
    vg
    cv
    vf
    cv
    @2
    vy
    cv
    #
    cop
    vz
    cv
    #
    @0
    cco
    cfv
    #
    co
    co
    @2
    @6
    cH
    co
    wcel
    #
    vg
    @5
    @6
    cH
    co
    #
    wral
    vf
    @2
    @5
    cH
    co
    #
    wral
    #
    vz
    cR
    wral
    vy
    cR
    wral
    #
    wa
    #
    vx
    cR
    wral
    wph
    crh
    cR
    cR
    cxp
    cres
    #
    crngh
    crng
    cU
    cin
    #
    @15
    cxp
    cres
    cH
    @1
    cssc
    wph
    cR
    @15
    cU
    cV
    rngcrescrhmALTV.u
    rngcrescrhmALTV.r
    wph
    @15
    eqidd
    rhmsscrnghm
    cH
    @14
    wceq
    wph
    rngcrescrhmALTV.h
    a1i
    wph
    @15
    @0
    cU
    @1
    cV
    @0
    eqid
    #
    @15
    eqid
    rngcrescrhmALTV.u
    @1
    eqid
    #
    rngchomrnghmresALTV
    3brtr4d
    wph
    @13
    vx
    cR
    wph
    @2
    cR
    wcel
    wa
    #
    @4
    @12
    wph
    vx
    cC
    cR
    cU
    cH
    cV
    rngcrescrhmALTV.u
    rngcrescrhmALTV.c
    rngcrescrhmALTV.r
    rngcrescrhmALTV.h
    rhmsubcALTVlem3
    @18
    @11
    vy
    vz
    cR
    cR
    @18
    @5
    cR
    wcel
    @6
    cR
    wcel
    wa
    wa
    @8
    vf
    vg
    @10
    @9
    wph
    vx
    vy
    vz
    cC
    cR
    cU
    vf
    vg
    cH
    cV
    rngcrescrhmALTV.u
    rngcrescrhmALTV.c
    rngcrescrhmALTV.r
    rngcrescrhmALTV.h
    rhmsubcALTVlem4
    ralrimivva
    ralrimivva
    jca
    ralrimiva
    wph
    vx
    vy
    vz
    @0
    cR
    @7
    @3
    vf
    vg
    @1
    cH
    @17
    @3
    eqid
    @7
    eqid
    wph
    cU
    cV
    wcel
    @0
    ccat
    wcel
    rngcrescrhmALTV.u
    @0
    cU
    cV
    @16
    rngccatALTV
    syl
    wph
    cC
    cR
    cU
    cH
    cV
    rngcrescrhmALTV.u
    rngcrescrhmALTV.c
    rngcrescrhmALTV.r
    rngcrescrhmALTV.h
    rhmsubcALTVlem1
    issubc2
    mpbir2and
end
