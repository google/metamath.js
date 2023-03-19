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
include "cbs.mm"
include "cmap.mm"
include "cmpt2.mm"
include "rhmsscmap.mm"
include "chom.mm"
include "eqid.mm"
include "estrchomfeqhom.mm"
include "estrchomfval.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "rhmsubcsetclem1.mm"
include "rhmsubcsetclem2.mm"
include "jca.mm"
include "ralrimiva.mm"
include "ccat.mm"
include "estrccat.mm"
include "syl.mm"
include "crg.mm"
include "cin.mm"
include "incom.mm"
include "syl6eq.mm"
include "rhmresfn.mm"
include "issubc2.mm"
include "mpbir2and.mm"

theorem rhmsubcsetc
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
  assume rhmsubcsetc.c: |- C = ( ExtStrCat ` U )
  assume rhmsubcsetc.u: |- ( ph -> U e. V )
  assume rhmsubcsetc.b: |- ( ph -> B = ( Ring i^i U ) )
  assume rhmsubcsetc.h: |- ( ph -> H = ( RingHom |` ( B X. B ) ) )


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
    rhmsubcsetc.u
    rhmsubcsetc.b
    rhmsscmap
    rhmsubcsetc.h
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
    rhmsubcsetc.c
    rhmsubcsetc.u
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
    rhmsubcsetc.c
    rhmsubcsetc.u
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
    rhmsubcsetc.c
    rhmsubcsetc.u
    rhmsubcsetc.b
    rhmsubcsetc.h
    rhmsubcsetclem1
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
    rhmsubcsetc.c
    rhmsubcsetc.u
    rhmsubcsetc.b
    rhmsubcsetc.h
    rhmsubcsetclem2
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
    rhmsubcsetc.u
    cC
    cU
    cV
    rhmsubcsetc.c
    estrccat
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
    rhmsubcsetc.b
    crg
    cU
    incom
    syl6eq
    rhmsubcsetc.h
    rhmresfn
    issubc2
    mpbir2and
end
