include "co.mm"
include "wbr.mm"
include "csect.mm"
include "cfv.mm"
include "wa.mm"
include "wf.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "wf1o.mm"
include "ccnv.mm"
include "cbs.mm"
include "eqid.mm"
include "wcel.mm"
include "ccat.mm"
include "setccat.mm"
include "syl.mm"
include "setcbas.mm"
include "eleqtrd.mm"
include "isinv.mm"
include "w3a.mm"
include "setcsect.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "3ancoma.mm"
include "bitri.mm"
include "anbi12d.mm"
include "anandi.mm"
include "syl6bbr.mm"
include "fcof1o.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "sylib.mm"
include "ancom2s.mm"
include "adantl.mm"
include "f1of.mm"
include "ad2antrl.mm"
include "f1ocnv.mm"
include "wb.mm"
include "f1oeq1.mm"
include "ad2antll.mm"
include "mpbird.mm"
include "simprr.mm"
include "coeq1d.mm"
include "f1ococnv1.mm"
include "eqtrd.mm"
include "coeq2d.mm"
include "f1ococnv2.mm"
include "jca.mm"
include "jca31.mm"
include "impbida.mm"
include "3bitrd.mm"

theorem setcinv
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cF: class F
  let cG: class G
  let cN: class N
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
  assume setcinv.n: |- N = ( Inv ` C )


  assert |- ( ph -> ( F ( X N Y ) G <-> ( F : X -1-1-onto-> Y /\ G = `' F ) ) )

  proof
    wph
    cF
    cG
    cX
    cY
    cN
    co
    wbr
    cF
    cG
    cX
    cY
    cC
    csect
    cfv
    #
    co
    wbr
    #
    cG
    cF
    cY
    cX
    @0
    co
    wbr
    #
    wa
    #
    cX
    cY
    cF
    wf
    #
    cY
    cX
    cG
    wf
    #
    wa
    #
    cG
    cF
    ccom
    #
    cid
    cX
    cres
    #
    wceq
    #
    cF
    cG
    ccom
    #
    cid
    cY
    cres
    #
    wceq
    #
    wa
    #
    wa
    #
    cX
    cY
    cF
    wf1o
    #
    cG
    cF
    ccnv
    #
    wceq
    #
    wa
    #
    wph
    cC
    cbs
    cfv
    #
    cC
    @0
    cF
    cG
    cN
    cX
    cY
    @19
    eqid
    setcinv.n
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
    wph
    cX
    cU
    @19
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
    wph
    cY
    cU
    @19
    setcmon.y
    @20
    eleqtrd
    @0
    eqid
    #
    isinv
    wph
    @3
    @6
    @9
    wa
    #
    @6
    @12
    wa
    #
    wa
    @14
    wph
    @1
    @22
    @2
    @23
    wph
    @1
    @4
    @5
    @9
    w3a
    @22
    wph
    cC
    @0
    cU
    cF
    cG
    cV
    cX
    cY
    setcmon.c
    setcmon.u
    setcmon.x
    setcmon.y
    @21
    setcsect
    @4
    @5
    @9
    df-3an
    syl6bb
    wph
    @2
    @5
    @4
    @12
    w3a
    #
    @23
    wph
    cC
    @0
    cU
    cG
    cF
    cV
    cY
    cX
    setcmon.c
    setcmon.u
    setcmon.y
    setcmon.x
    @21
    setcsect
    @24
    @4
    @5
    @12
    w3a
    @23
    @5
    @4
    @12
    3ancoma
    @4
    @5
    @12
    df-3an
    bitri
    syl6bb
    anbi12d
    @6
    @9
    @12
    anandi
    syl6bbr
    wph
    @14
    @18
    @14
    @18
    wph
    @6
    @12
    @9
    @18
    @6
    @12
    @9
    wa
    wa
    @15
    @16
    cG
    wceq
    #
    wa
    @18
    cX
    cY
    cF
    cG
    fcof1o
    @25
    @17
    @15
    @16
    cG
    eqcom
    anbi2i
    sylib
    ancom2s
    adantl
    wph
    @18
    wa
    #
    @4
    @5
    @13
    @15
    @4
    wph
    @17
    cX
    cY
    cF
    f1of
    ad2antrl
    @26
    cY
    cX
    cG
    wf1o
    #
    @5
    @26
    @27
    cY
    cX
    @16
    wf1o
    #
    @15
    @28
    wph
    @17
    cX
    cY
    cF
    f1ocnv
    ad2antrl
    @17
    @27
    @28
    wb
    wph
    @15
    cY
    cX
    cG
    @16
    f1oeq1
    ad2antll
    mpbird
    cY
    cX
    cG
    f1of
    syl
    @26
    @9
    @12
    @26
    @7
    @16
    cF
    ccom
    #
    @8
    @26
    cG
    @16
    cF
    wph
    @15
    @17
    simprr
    #
    coeq1d
    @15
    @29
    @8
    wceq
    wph
    @17
    cX
    cY
    cF
    f1ococnv1
    ad2antrl
    eqtrd
    @26
    @10
    cF
    @16
    ccom
    #
    @11
    @26
    cG
    @16
    cF
    @30
    coeq2d
    @15
    @31
    @11
    wceq
    wph
    @17
    cX
    cY
    cF
    f1ococnv2
    ad2antrl
    eqtrd
    jca
    jca31
    impbida
    3bitrd
end
