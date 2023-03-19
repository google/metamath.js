include "cestrc.mm"
include "cfv.mm"
include "cresc.mm"
include "co.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "chom.mm"
include "cco.mm"
include "ctp.mm"
include "rngcval.mm"
include "cress.mm"
include "csts.mm"
include "cvv.mm"
include "eqid.mm"
include "fvexd.mm"
include "crng.mm"
include "cin.mm"
include "wcel.mm"
include "inex1g.mm"
include "syl.mm"
include "eqeltrd.mm"
include "rnghmresfn.mm"
include "rescval2.mm"
include "cv.mm"
include "cmap.mm"
include "cmpt2.mm"
include "eqidd.mm"
include "cxp.mm"
include "c2nd.mm"
include "c1st.mm"
include "ccom.mm"
include "estrccofval.mm"
include "eqtrd.mm"
include "estrcval.mm"
include "wa.mm"
include "jca.mm"
include "mpt2exg.mm"
include "crngh.mm"
include "cres.mm"
include "wfun.mm"
include "wfn.mm"
include "rnghmfn.mm"
include "fnfun.mm"
include "mp1i.mm"
include "sqxpexg.mm"
include "resfunexg.mm"
include "syl2anc.mm"
include "wss.mm"
include "inss1.mm"
include "a1i.mm"
include "sseq1d.mm"
include "mpbird.mm"
include "estrres.mm"

theorem dfrngc2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cU: class U
  let cH: class H
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume dfrngc2.c: |- C = ( RngCat ` U )
  assume dfrngc2.u: |- ( ph -> U e. V )
  assume dfrngc2.b: |- ( ph -> B = ( U i^i Rng ) )
  assume dfrngc2.h: |- ( ph -> H = ( RngHomo |` ( B X. B ) ) )
  assume dfrngc2.o: |- ( ph -> .x. = ( comp ` ( ExtStrCat ` U ) ) )


  assert |- ( ph -> C = { <. ( Base ` ndx ) , B >. , <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .x. >. } )

  proof
    wph
    cC
    cU
    cestrc
    cfv
    #
    cH
    cresc
    co
    #
    cnx
    cbs
    cfv
    cB
    cop
    cnx
    chom
    cfv
    cH
    cop
    #
    cnx
    cco
    cfv
    c.x
    cop
    ctp
    #
    wph
    cB
    cC
    cU
    cH
    cV
    dfrngc2.c
    dfrngc2.u
    dfrngc2.b
    dfrngc2.h
    rngcval
    wph
    @1
    @0
    cB
    cress
    co
    @2
    csts
    co
    @3
    wph
    @0
    @1
    cB
    cH
    cvv
    cvv
    @1
    eqid
    wph
    cU
    cestrc
    fvexd
    wph
    cB
    cU
    crng
    cin
    #
    cvv
    dfrngc2.b
    wph
    cU
    cV
    wcel
    #
    @4
    cvv
    wcel
    dfrngc2.u
    cU
    crng
    cV
    inex1g
    syl
    eqeltrd
    #
    wph
    cB
    cU
    cH
    dfrngc2.b
    dfrngc2.h
    rnghmresfn
    rescval2
    wph
    cB
    cU
    @0
    c.x
    cvv
    cH
    vx
    vy
    cU
    cU
    vy
    cv
    cbs
    cfv
    vx
    cv
    cbs
    cfv
    cmap
    co
    #
    cmpt2
    #
    cV
    cvv
    cvv
    cvv
    wph
    vx
    vy
    vz
    vv
    @0
    c.x
    cU
    vf
    vg
    @8
    cV
    @0
    eqid
    #
    dfrngc2.u
    wph
    @8
    eqidd
    wph
    c.x
    @0
    cco
    cfv
    #
    vv
    vz
    cU
    cU
    cxp
    cU
    vg
    vf
    vz
    cv
    cbs
    cfv
    vv
    cv
    #
    c2nd
    cfv
    cbs
    cfv
    #
    cmap
    co
    @12
    @11
    c1st
    cfv
    cbs
    cfv
    cmap
    co
    vg
    cv
    vf
    cv
    ccom
    cmpt2
    cmpt2
    dfrngc2.o
    wph
    vz
    vv
    @0
    @10
    cU
    vf
    vg
    cV
    @9
    dfrngc2.u
    @10
    eqid
    estrccofval
    eqtrd
    estrcval
    dfrngc2.u
    wph
    @5
    @5
    wa
    @8
    cvv
    wcel
    wph
    @5
    @5
    dfrngc2.u
    dfrngc2.u
    jca
    vx
    vy
    cU
    cU
    @7
    cV
    cV
    @8
    @8
    eqid
    mpt2exg
    syl
    wph
    c.x
    @10
    cvv
    dfrngc2.o
    wph
    @0
    cco
    fvexd
    eqeltrd
    @6
    wph
    cH
    crngh
    cB
    cB
    cxp
    #
    cres
    #
    cvv
    dfrngc2.h
    wph
    crngh
    wfun
    #
    @13
    cvv
    wcel
    #
    @14
    cvv
    wcel
    crngh
    crng
    crng
    cxp
    #
    wfn
    @15
    wph
    rnghmfn
    @17
    crngh
    fnfun
    mp1i
    wph
    cB
    cvv
    wcel
    @16
    @6
    cB
    cvv
    sqxpexg
    syl
    crngh
    @13
    cvv
    resfunexg
    syl2anc
    eqeltrd
    wph
    cB
    cU
    wss
    @4
    cU
    wss
    #
    @18
    wph
    cU
    crng
    inss1
    a1i
    wph
    cB
    @4
    cU
    dfrngc2.b
    sseq1d
    mpbird
    estrres
    eqtrd
    eqtrd
end
