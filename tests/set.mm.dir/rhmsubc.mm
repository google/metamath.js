include "crngc.mm"
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
include "chom.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "cbs.mm"
include "eqid.mm"
include "rngchomfeqhom.mm"
include "rngchomfval.mm"
include "rngcbas.mm"
include "incom.mm"
include "syl6eq.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "3brtr4d.mm"
include "rhmsubclem3.mm"
include "rhmsubclem4.mm"
include "ralrimivva.mm"
include "jca.mm"
include "ralrimiva.mm"
include "ccat.mm"
include "rngccat.mm"
include "syl.mm"
include "rhmsubclem1.mm"
include "issubc2.mm"
include "mpbir2and.mm"

theorem rhmsubc
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
  assume rngcrescrhm.u: |- ( ph -> U e. V )
  assume rngcrescrhm.c: |- C = ( RngCat ` U )
  assume rngcrescrhm.r: |- ( ph -> R = ( Ring i^i U ) )
  assume rngcrescrhm.h: |- H = ( RingHom |` ( R X. R ) )


  assert |- ( ph -> H e. ( Subcat ` ( RngCat ` U ) ) )

  proof
    wph
    cH
    cU
    crngc
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
    #
    cres
    #
    cH
    @1
    cssc
    wph
    cR
    @15
    cU
    cV
    rngcrescrhm.u
    rngcrescrhm.r
    wph
    @15
    eqidd
    rhmsscrnghm
    cH
    @14
    wceq
    wph
    rngcrescrhm.h
    a1i
    wph
    @1
    cC
    chomf
    cfv
    cC
    chom
    cfv
    #
    @17
    wph
    @0
    cC
    chomf
    wph
    cC
    @0
    cC
    @0
    wceq
    wph
    rngcrescrhm.c
    a1i
    eqcomd
    fveq2d
    wph
    cC
    cbs
    cfv
    #
    cC
    cU
    cV
    rngcrescrhm.c
    @19
    eqid
    #
    rngcrescrhm.u
    rngchomfeqhom
    wph
    @18
    crngh
    @19
    @19
    cxp
    #
    cres
    @17
    wph
    @19
    cC
    cU
    @18
    cV
    rngcrescrhm.c
    @20
    rngcrescrhm.u
    @18
    eqid
    rngchomfval
    wph
    @21
    @16
    crngh
    wph
    @19
    @15
    wph
    @19
    cU
    crng
    cin
    @15
    wph
    @19
    cC
    cU
    cV
    rngcrescrhm.c
    @20
    rngcrescrhm.u
    rngcbas
    cU
    crng
    incom
    syl6eq
    sqxpeqd
    reseq2d
    eqtrd
    3eqtrd
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
    rngcrescrhm.u
    rngcrescrhm.c
    rngcrescrhm.r
    rngcrescrhm.h
    rhmsubclem3
    @22
    @11
    vy
    vz
    cR
    cR
    @22
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
    rngcrescrhm.u
    rngcrescrhm.c
    rngcrescrhm.r
    rngcrescrhm.h
    rhmsubclem4
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
    @1
    eqid
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
    rngcrescrhm.u
    @0
    cU
    cV
    @0
    eqid
    rngccat
    syl
    wph
    cC
    cR
    cU
    cH
    cV
    rngcrescrhm.u
    rngcrescrhm.c
    rngcrescrhm.r
    rngcrescrhm.h
    rhmsubclem1
    issubc2
    mpbir2and
end
