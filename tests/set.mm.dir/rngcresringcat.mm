include "cress.mm"
include "co.mm"
include "cnx.mm"
include "chom.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "cbs.mm"
include "cco.mm"
include "cestrc.mm"
include "ctp.mm"
include "cresc.mm"
include "cringc.mm"
include "crng.mm"
include "cin.mm"
include "cvv.mm"
include "crngh.mm"
include "cxp.mm"
include "cres.mm"
include "eqidd.mm"
include "dfrngc2.mm"
include "wcel.mm"
include "inex1g.mm"
include "syl.mm"
include "wfun.mm"
include "wfn.mm"
include "rnghmfn.mm"
include "fnfun.mm"
include "mp1i.mm"
include "sqxpexg.mm"
include "resfunexg.mm"
include "syl2anc.mm"
include "fvexd.mm"
include "crg.mm"
include "incom.mm"
include "syl6eq.mm"
include "eqeltrd.mm"
include "crh.mm"
include "rhmfn.mm"
include "wss.mm"
include "cv.mm"
include "wi.mm"
include "ringrng.mm"
include "a1i.mm"
include "ssrdv.mm"
include "ssrin.mm"
include "wceq.mm"
include "3sstr4d.mm"
include "estrres.mm"
include "eqid.mm"
include "crngc.mm"
include "rhmresfn.mm"
include "rescval2.mm"
include "dfringc2.mm"
include "3eqtr4d.mm"

theorem rngcresringcat
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
  let vr: setvar r
  let vk: setvar k
  assume rhmsubcrngc.c: |- C = ( RngCat ` U )
  assume rhmsubcrngc.u: |- ( ph -> U e. V )
  assume rhmsubcrngc.b: |- ( ph -> B = ( Ring i^i U ) )
  assume rhmsubcrngc.h: |- ( ph -> H = ( RingHom |` ( B X. B ) ) )


  assert |- ( ph -> ( C |`cat H ) = ( RingCat ` U ) )

  proof
    wph
    cC
    cB
    cress
    co
    cnx
    chom
    cfv
    cH
    cop
    #
    csts
    co
    cnx
    cbs
    cfv
    cB
    cop
    @0
    cnx
    cco
    cfv
    cU
    cestrc
    cfv
    #
    cco
    cfv
    #
    cop
    ctp
    cC
    cH
    cresc
    co
    #
    cU
    cringc
    cfv
    #
    wph
    cB
    cU
    crng
    cin
    #
    cC
    @2
    cvv
    cH
    crngh
    @5
    @5
    cxp
    #
    cres
    #
    cvv
    cvv
    cvv
    cvv
    wph
    @5
    cC
    @2
    cU
    @7
    cV
    rhmsubcrngc.c
    rhmsubcrngc.u
    wph
    @5
    eqidd
    wph
    @7
    eqidd
    wph
    @2
    eqidd
    #
    dfrngc2
    wph
    cU
    cV
    wcel
    #
    @5
    cvv
    wcel
    #
    rhmsubcrngc.u
    cU
    crng
    cV
    inex1g
    syl
    #
    wph
    crngh
    wfun
    #
    @6
    cvv
    wcel
    #
    @7
    cvv
    wcel
    crngh
    crng
    crng
    cxp
    #
    wfn
    @12
    wph
    rnghmfn
    @14
    crngh
    fnfun
    mp1i
    wph
    @10
    @13
    @11
    @5
    cvv
    sqxpexg
    syl
    crngh
    @6
    cvv
    resfunexg
    syl2anc
    wph
    @1
    cco
    fvexd
    wph
    cB
    cU
    crg
    cin
    #
    cvv
    wph
    cB
    crg
    cU
    cin
    #
    @15
    rhmsubcrngc.b
    crg
    cU
    incom
    syl6eq
    #
    wph
    @9
    @15
    cvv
    wcel
    rhmsubcrngc.u
    cU
    crg
    cV
    inex1g
    syl
    eqeltrd
    #
    wph
    cH
    crh
    cB
    cB
    cxp
    #
    cres
    #
    cvv
    rhmsubcrngc.h
    wph
    crh
    wfun
    #
    @19
    cvv
    wcel
    #
    @20
    cvv
    wcel
    crh
    crg
    crg
    cxp
    #
    wfn
    @21
    wph
    rhmfn
    @23
    crh
    fnfun
    mp1i
    wph
    cB
    cvv
    wcel
    @22
    @18
    cB
    cvv
    sqxpexg
    syl
    crh
    @19
    cvv
    resfunexg
    syl2anc
    eqeltrd
    wph
    @16
    crng
    cU
    cin
    #
    cB
    @5
    wph
    crg
    crng
    wss
    @16
    @24
    wss
    wph
    vr
    crg
    crng
    vr
    cv
    #
    crg
    wcel
    @25
    crng
    wcel
    wi
    wph
    @25
    ringrng
    a1i
    ssrdv
    crg
    crng
    cU
    ssrin
    syl
    rhmsubcrngc.b
    @5
    @24
    wceq
    wph
    cU
    crng
    incom
    a1i
    3sstr4d
    estrres
    wph
    cC
    @3
    cB
    cH
    cvv
    cvv
    @3
    eqid
    wph
    cC
    cU
    crngc
    cfv
    #
    cvv
    cC
    @26
    wceq
    wph
    rhmsubcrngc.c
    a1i
    wph
    cU
    crngc
    fvexd
    eqeltrd
    @18
    wph
    cB
    cU
    cH
    @17
    rhmsubcrngc.h
    rhmresfn
    rescval2
    wph
    cB
    @4
    @2
    cU
    cH
    cV
    @4
    eqid
    rhmsubcrngc.u
    @17
    rhmsubcrngc.h
    @8
    dfringc2
    3eqtr4d
end
