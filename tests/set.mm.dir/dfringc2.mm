include "cestrc.mm"
include "cfv.mm"
include "cresc.mm"
include "co.mm"
include "cress.mm"
include "cnx.mm"
include "chom.mm"
include "cop.mm"
include "csts.mm"
include "cbs.mm"
include "cco.mm"
include "ctp.mm"
include "ringcval.mm"
include "cvv.mm"
include "eqid.mm"
include "fvexd.mm"
include "crg.mm"
include "cin.mm"
include "wcel.mm"
include "inex1g.mm"
include "syl.mm"
include "eqeltrd.mm"
include "rhmresfn.mm"
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
include "mpt2exg.mm"
include "syl2anc.mm"
include "crh.mm"
include "cres.mm"
include "wfun.mm"
include "wfn.mm"
include "rhmfn.mm"
include "fnfun.mm"
include "mp1i.mm"
include "sqxpexg.mm"
include "resfunexg.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "estrres.mm"
include "3eqtrd.mm"

theorem dfringc2
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
  assume dfringc2.c: |- C = ( RingCat ` U )
  assume dfringc2.u: |- ( ph -> U e. V )
  assume dfringc2.b: |- ( ph -> B = ( U i^i Ring ) )
  assume dfringc2.h: |- ( ph -> H = ( RingHom |` ( B X. B ) ) )
  assume dfringc2.o: |- ( ph -> .x. = ( comp ` ( ExtStrCat ` U ) ) )


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
    @0
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
    @2
    cnx
    cco
    cfv
    c.x
    cop
    ctp
    wph
    cB
    cC
    cU
    cH
    cV
    dfringc2.c
    dfringc2.u
    dfringc2.b
    dfringc2.h
    ringcval
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
    crg
    cin
    #
    cvv
    dfringc2.b
    wph
    cU
    cV
    wcel
    #
    @3
    cvv
    wcel
    dfringc2.u
    cU
    crg
    cV
    inex1g
    syl
    eqeltrd
    #
    wph
    cB
    cU
    cH
    dfringc2.b
    dfringc2.h
    rhmresfn
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
    @7
    cV
    @0
    eqid
    #
    dfringc2.u
    wph
    @7
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
    @11
    @10
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
    dfringc2.o
    wph
    vz
    vv
    @0
    @9
    cU
    vf
    vg
    cV
    @8
    dfringc2.u
    @9
    eqid
    estrccofval
    eqtrd
    estrcval
    dfringc2.u
    wph
    @4
    @4
    @7
    cvv
    wcel
    dfringc2.u
    dfringc2.u
    vx
    vy
    cU
    cU
    @6
    cV
    cV
    @7
    @7
    eqid
    mpt2exg
    syl2anc
    wph
    c.x
    @9
    cvv
    dfringc2.o
    wph
    @0
    cco
    fvexd
    eqeltrd
    @5
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
    dfringc2.h
    wph
    crh
    wfun
    #
    @12
    cvv
    wcel
    #
    @13
    cvv
    wcel
    crh
    crg
    crg
    cxp
    #
    wfn
    @14
    wph
    rhmfn
    @16
    crh
    fnfun
    mp1i
    wph
    cB
    cvv
    wcel
    @15
    @5
    cB
    cvv
    sqxpexg
    syl
    crh
    @12
    cvv
    resfunexg
    syl2anc
    eqeltrd
    wph
    cB
    @3
    cU
    dfringc2.b
    cU
    crg
    inss1
    syl6eqss
    estrres
    3eqtrd
end
