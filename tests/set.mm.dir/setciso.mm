include "co.mm"
include "wcel.mm"
include "cinv.mm"
include "cfv.mm"
include "cdm.mm"
include "wf1o.mm"
include "cbs.mm"
include "eqid.mm"
include "ccat.mm"
include "setccat.mm"
include "syl.mm"
include "setcbas.mm"
include "eleqtrd.mm"
include "isoval.mm"
include "eleq2d.mm"
include "wbr.mm"
include "wfun.mm"
include "wb.mm"
include "invfun.mm"
include "funfvbrb.mm"
include "ccnv.mm"
include "wceq.mm"
include "wa.mm"
include "setcinv.mm"
include "simpl.mm"
include "syl6bi.mm"
include "sylbid.mm"
include "wrel.mm"
include "wi.mm"
include "funrel.mm"
include "releldm.mm"
include "ex.mm"
include "sylbird.mm"
include "mpan2i.mm"
include "impbid.mm"
include "bitrd.mm"

theorem setciso
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cF: class F
  let cI: class I
  let cV: class V
  let cX: class X
  let cY: class Y
  let cE: class E
  let vx: setvar x
  let va: setvar a
  let vg: setvar g
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  assume setcmon.c: |- C = ( SetCat ` U )
  assume setcmon.u: |- ( ph -> U e. V )
  assume setcmon.x: |- ( ph -> X e. U )
  assume setcmon.y: |- ( ph -> Y e. U )
  assume setciso.n: |- I = ( Iso ` C )


  assert |- ( ph -> ( F e. ( X I Y ) <-> F : X -1-1-onto-> Y ) )

  proof
    wph
    cF
    cX
    cY
    cI
    co
    #
    wcel
    cF
    cX
    cY
    cC
    cinv
    cfv
    #
    co
    #
    cdm
    #
    wcel
    #
    cX
    cY
    cF
    wf1o
    #
    wph
    @0
    @3
    cF
    wph
    cC
    cbs
    cfv
    #
    cC
    cI
    @1
    cX
    cY
    @6
    eqid
    #
    @1
    eqid
    #
    wph
    cU
    cV
    wcel
    cC
    ccat
    wcel
    setcmon.u
    cC
    cU
    cV
    setcmon.c
    setccat
    syl
    #
    wph
    cX
    cU
    @6
    setcmon.x
    wph
    cC
    cU
    cV
    setcmon.c
    setcmon.u
    setcbas
    #
    eleqtrd
    #
    wph
    cY
    cU
    @6
    setcmon.y
    @10
    eleqtrd
    #
    setciso.n
    isoval
    eleq2d
    wph
    @4
    @5
    wph
    @4
    cF
    cF
    @2
    cfv
    #
    @2
    wbr
    #
    @5
    wph
    @2
    wfun
    #
    @4
    @14
    wb
    wph
    @6
    cC
    @1
    cX
    cY
    @7
    @8
    @9
    @11
    @12
    invfun
    #
    cF
    @2
    funfvbrb
    syl
    wph
    @14
    @5
    @13
    cF
    ccnv
    #
    wceq
    #
    wa
    @5
    wph
    cC
    cU
    cF
    @13
    @1
    cV
    cX
    cY
    setcmon.c
    setcmon.u
    setcmon.x
    setcmon.y
    @8
    setcinv
    @5
    @18
    simpl
    syl6bi
    sylbid
    wph
    @5
    @17
    @17
    wceq
    #
    @4
    @17
    eqid
    wph
    @5
    @19
    wa
    cF
    @17
    @2
    wbr
    #
    @4
    wph
    cC
    cU
    cF
    @17
    @1
    cV
    cX
    cY
    setcmon.c
    setcmon.u
    setcmon.x
    setcmon.y
    @8
    setcinv
    wph
    @2
    wrel
    #
    @20
    @4
    wi
    wph
    @15
    @21
    @16
    @2
    funrel
    syl
    @21
    @20
    @4
    cF
    @17
    @2
    releldm
    ex
    syl
    sylbird
    mpan2i
    impbid
    bitrd
end
