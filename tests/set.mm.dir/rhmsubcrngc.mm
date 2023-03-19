include "csubc.mm"
include "cfv.mm"
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
include "cbs.mm"
include "crngc.mm"
include "crng.mm"
include "cin.mm"
include "eqid.mm"
include "rngcbas.mm"
include "incom.mm"
include "syl6eq.mm"
include "rhmsscrnghm.mm"
include "wceq.mm"
include "a1i.mm"
include "fveq2d.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "breqtrrd.mm"
include "chom.mm"
include "rngchomfeqhom.mm"
include "rngchomfval.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "rhmsubcrngclem1.mm"
include "rhmsubcrngclem2.mm"
include "jca.mm"
include "ralrimiva.mm"
include "ccat.mm"
include "rngccat.mm"
include "syl.mm"
include "crg.mm"
include "rhmresfn.mm"
include "issubc2.mm"
include "mpbir2and.mm"

theorem rhmsubcrngc
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume rhmsubcrngc.c: |- C = ( RngCat ` U )
  assume rhmsubcrngc.u: |- ( ph -> U e. V )
  assume rhmsubcrngc.b: |- ( ph -> B = ( Ring i^i U ) )
  assume rhmsubcrngc.h: |- ( ph -> H = ( RingHom |` ( B X. B ) ) )


  assert |- ( ph -> H e. ( Subcat ` C ) )

  proof
    wph
    cH
    cC
    csubc
    cfv
    wcel
    cH
    cC
    chomf
    cfv
    #
    cssc
    wbr
    vx
    cv
    #
    cC
    ccid
    cfv
    #
    cfv
    @1
    @1
    cH
    co
    wcel
    #
    vg
    cv
    vf
    cv
    @1
    vy
    cv
    #
    cop
    vz
    cv
    #
    cC
    cco
    cfv
    #
    co
    co
    @1
    @5
    cH
    co
    wcel
    vg
    @4
    @5
    cH
    co
    wral
    vf
    @1
    @4
    cH
    co
    wral
    vz
    cB
    wral
    vy
    cB
    wral
    #
    wa
    #
    vx
    cB
    wral
    wph
    crh
    cB
    cB
    cxp
    cres
    #
    crngh
    cC
    cbs
    cfv
    #
    @10
    cxp
    #
    cres
    #
    cH
    @0
    cssc
    wph
    @9
    crngh
    cU
    crngc
    cfv
    #
    cbs
    cfv
    #
    @14
    cxp
    #
    cres
    @12
    cssc
    wph
    cB
    @14
    cU
    cV
    rhmsubcrngc.u
    rhmsubcrngc.b
    wph
    @14
    cU
    crng
    cin
    crng
    cU
    cin
    wph
    @14
    @13
    cU
    cV
    @13
    eqid
    @14
    eqid
    rhmsubcrngc.u
    rngcbas
    cU
    crng
    incom
    syl6eq
    rhmsscrnghm
    wph
    @11
    @15
    crngh
    wph
    @10
    @14
    wph
    cC
    @13
    cbs
    cC
    @13
    wceq
    wph
    rhmsubcrngc.c
    a1i
    fveq2d
    sqxpeqd
    reseq2d
    breqtrrd
    rhmsubcrngc.h
    wph
    @0
    cC
    chom
    cfv
    #
    @12
    wph
    @10
    cC
    cU
    cV
    rhmsubcrngc.c
    @10
    eqid
    #
    rhmsubcrngc.u
    rngchomfeqhom
    wph
    @10
    cC
    cU
    @16
    cV
    rhmsubcrngc.c
    @17
    rhmsubcrngc.u
    @16
    eqid
    rngchomfval
    eqtrd
    3brtr4d
    wph
    @8
    vx
    cB
    wph
    @1
    cB
    wcel
    wa
    @3
    @7
    wph
    vx
    cB
    cC
    cU
    cH
    cV
    rhmsubcrngc.c
    rhmsubcrngc.u
    rhmsubcrngc.b
    rhmsubcrngc.h
    rhmsubcrngclem1
    wph
    vx
    vy
    vz
    cB
    cC
    cU
    vf
    vg
    cH
    cV
    rhmsubcrngc.c
    rhmsubcrngc.u
    rhmsubcrngc.b
    rhmsubcrngc.h
    rhmsubcrngclem2
    jca
    ralrimiva
    wph
    vx
    vy
    vz
    cC
    cB
    @6
    @2
    vf
    vg
    @0
    cH
    @0
    eqid
    @2
    eqid
    @6
    eqid
    wph
    cU
    cV
    wcel
    cC
    ccat
    wcel
    rhmsubcrngc.u
    cC
    cU
    cV
    rhmsubcrngc.c
    rngccat
    syl
    wph
    cB
    cU
    cH
    wph
    cB
    crg
    cU
    cin
    cU
    crg
    cin
    rhmsubcrngc.b
    crg
    cU
    incom
    syl6eq
    rhmsubcrngc.h
    rhmresfn
    issubc2
    mpbir2and
end
