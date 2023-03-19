include "cxp.mm"
include "wfn.mm"
include "cv.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "cin.mm"
include "cmpt2.mm"
include "eqid.mm"
include "ovex.mm"
include "inex1.mm"
include "fnmpt2i.mm"
include "crh.mm"
include "cres.mm"
include "crg.mm"
include "wceq.mm"
include "a1i.mm"
include "dfrhm2.mm"
include "reseq1d.mm"
include "wss.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "resmpt2.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem rhmsubcALTVlem1
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cU: class U
  let cH: class H
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume rngcrescrhmALTV.u: |- ( ph -> U e. V )
  assume rngcrescrhmALTV.c: |- C = ( RngCatALTV ` U )
  assume rngcrescrhmALTV.r: |- ( ph -> R = ( Ring i^i U ) )
  assume rngcrescrhmALTV.h: |- H = ( RingHom |` ( R X. R ) )


  assert |- ( ph -> H Fn ( R X. R ) )

  proof
    wph
    cH
    cR
    cR
    cxp
    #
    wfn
    vx
    vy
    cR
    cR
    vx
    cv
    #
    vy
    cv
    #
    cghm
    co
    #
    @1
    cmgp
    cfv
    @2
    cmgp
    cfv
    cmhm
    co
    #
    cin
    #
    cmpt2
    #
    @0
    wfn
    vx
    vy
    cR
    cR
    @5
    @6
    @6
    eqid
    @3
    @4
    @1
    @2
    cghm
    ovex
    inex1
    fnmpt2i
    wph
    @0
    cH
    @6
    wph
    cH
    crh
    @0
    cres
    #
    vx
    vy
    crg
    crg
    @5
    cmpt2
    #
    @0
    cres
    #
    @6
    cH
    @7
    wceq
    wph
    rngcrescrhmALTV.h
    a1i
    wph
    crh
    @8
    @0
    crh
    @8
    wceq
    wph
    vy
    vx
    dfrhm2
    a1i
    reseq1d
    wph
    cR
    crg
    wss
    #
    @10
    @9
    @6
    wceq
    wph
    cR
    crg
    cU
    cin
    crg
    rngcrescrhmALTV.r
    crg
    cU
    inss1
    syl6eqss
    #
    @11
    vx
    vy
    crg
    crg
    cR
    cR
    @5
    resmpt2
    syl2anc
    3eqtrd
    fneq1d
    mpbiri
end
