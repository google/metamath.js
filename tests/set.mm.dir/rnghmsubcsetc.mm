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
include "crngh.mm"
include "cxp.mm"
include "cres.mm"
include "cbs.mm"
include "cmap.mm"
include "cmpt2.mm"
include "rnghmsscmap.mm"
include "chom.mm"
include "eqid.mm"
include "estrchomfeqhom.mm"
include "estrchomfval.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "rnghmsubcsetclem1.mm"
include "rnghmsubcsetclem2.mm"
include "jca.mm"
include "ralrimiva.mm"
include "ccat.mm"
include "estrccat.mm"
include "syl.mm"
include "crng.mm"
include "cin.mm"
include "incom.mm"
include "syl6eq.mm"
include "rnghmresfn.mm"
include "issubc2.mm"
include "mpbir2and.mm"

theorem rnghmsubcsetc
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
  assume rnghmsubcsetc.c: |- C = ( ExtStrCat ` U )
  assume rnghmsubcsetc.u: |- ( ph -> U e. V )
  assume rnghmsubcsetc.b: |- ( ph -> B = ( Rng i^i U ) )
  assume rnghmsubcsetc.h: |- ( ph -> H = ( RngHomo |` ( B X. B ) ) )


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
    crngh
    cB
    cB
    cxp
    cres
    vx
    vy
    cU
    cU
    @4
    cbs
    cfv
    @1
    cbs
    cfv
    cmap
    co
    cmpt2
    #
    cH
    @0
    cssc
    wph
    vx
    vy
    cB
    cU
    cV
    rnghmsubcsetc.u
    rnghmsubcsetc.b
    rnghmsscmap
    rnghmsubcsetc.h
    wph
    @0
    cC
    chom
    cfv
    #
    @9
    wph
    cC
    cU
    @10
    cV
    rnghmsubcsetc.c
    rnghmsubcsetc.u
    @10
    eqid
    #
    estrchomfeqhom
    wph
    vx
    vy
    cC
    cU
    @10
    cV
    rnghmsubcsetc.c
    rnghmsubcsetc.u
    @11
    estrchomfval
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
    rnghmsubcsetc.c
    rnghmsubcsetc.u
    rnghmsubcsetc.b
    rnghmsubcsetc.h
    rnghmsubcsetclem1
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
    rnghmsubcsetc.c
    rnghmsubcsetc.u
    rnghmsubcsetc.b
    rnghmsubcsetc.h
    rnghmsubcsetclem2
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
    rnghmsubcsetc.u
    cC
    cU
    cV
    rnghmsubcsetc.c
    estrccat
    syl
    wph
    cB
    cU
    cH
    wph
    cB
    crng
    cU
    cin
    cU
    crng
    cin
    rnghmsubcsetc.b
    crng
    cU
    incom
    syl6eq
    rnghmsubcsetc.h
    rnghmresfn
    issubc2
    mpbir2and
end
