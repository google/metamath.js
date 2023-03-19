include "cresc.mm"
include "co.mm"
include "cvv.mm"
include "eqid.mm"
include "wcel.mm"
include "crngc.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "crg.mm"
include "cin.mm"
include "incom.mm"
include "syl6eq.mm"
include "inex1g.mm"
include "syl.mm"
include "eqeltrd.mm"
include "crh.mm"
include "cxp.mm"
include "cres.mm"
include "wfn.mm"
include "wss.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "wb.mm"
include "rhmfn.mm"
include "fnssresb.mm"
include "mp1i.mm"
include "mpbird.mm"
include "fneq1i.mm"
include "sylibr.mm"
include "rescval2.mm"

theorem rngcrescrhm
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cU: class U
  let cH: class H
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume rngcrescrhm.u: |- ( ph -> U e. V )
  assume rngcrescrhm.c: |- C = ( RngCat ` U )
  assume rngcrescrhm.r: |- ( ph -> R = ( Ring i^i U ) )
  assume rngcrescrhm.h: |- H = ( RingHom |` ( R X. R ) )


  assert |- ( ph -> ( C |`cat H ) = ( ( C |`s R ) sSet <. ( Hom ` ndx ) , H >. ) )

  proof
    wph
    cC
    cC
    cH
    cresc
    co
    #
    cR
    cH
    cvv
    cvv
    @0
    eqid
    cC
    cvv
    wcel
    wph
    cC
    cU
    crngc
    cfv
    cvv
    rngcrescrhm.c
    cU
    crngc
    fvex
    eqeltri
    a1i
    wph
    cR
    cU
    crg
    cin
    #
    cvv
    wph
    cR
    crg
    cU
    cin
    #
    @1
    rngcrescrhm.r
    crg
    cU
    incom
    syl6eq
    wph
    cU
    cV
    wcel
    @1
    cvv
    wcel
    rngcrescrhm.u
    cU
    crg
    cV
    inex1g
    syl
    eqeltrd
    wph
    crh
    cR
    cR
    cxp
    #
    cres
    #
    @3
    wfn
    #
    cH
    @3
    wfn
    wph
    @5
    @3
    crg
    crg
    cxp
    #
    wss
    #
    wph
    cR
    crg
    wss
    #
    @8
    @7
    wph
    cR
    @2
    crg
    rngcrescrhm.r
    crg
    cU
    inss1
    syl6eqss
    #
    @9
    cR
    crg
    cR
    crg
    xpss12
    syl2anc
    crh
    @6
    wfn
    @5
    @7
    wb
    wph
    rhmfn
    @6
    @3
    crh
    fnssresb
    mp1i
    mpbird
    @3
    cH
    @4
    rngcrescrhm.h
    fneq1i
    sylibr
    rescval2
end
