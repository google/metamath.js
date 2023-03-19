include "cple.mm"
include "cfv.mm"
include "ccom.mm"
include "ccnv.mm"
include "cxp.mm"
include "eqid.mm"
include "imasle.mm"
include "cdm.mm"
include "crn.mm"
include "wrel.mm"
include "wss.mm"
include "relco.mm"
include "relssdmrn.mm"
include "ax-mp.mm"
include "cima.mm"
include "dmco.mm"
include "wceq.mm"
include "wfo.mm"
include "wf.mm"
include "fof.mm"
include "frel.mm"
include "3syl.mm"
include "dfrel2.mm"
include "sylib.mm"
include "imaeq1d.mm"
include "imassrn.mm"
include "forn.mm"
include "syl.mm"
include "syl5sseq.mm"
include "eqsstrd.mm"
include "syl5eqss.mm"
include "rncoss.mm"
include "rnco2.mm"
include "syl5ss.mm"
include "xpss12.mm"
include "syl2anc.mm"

theorem imasless
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cF: class F
  let c.le: class .<_
  let cV: class V
  let cZ: class Z
  assume imasless.u: |- ( ph -> U = ( F "s R ) )
  assume imasless.v: |- ( ph -> V = ( Base ` R ) )
  assume imasless.f: |- ( ph -> F : V -onto-> B )
  assume imasless.r: |- ( ph -> R e. Z )
  assume imasless.l: |- .<_ = ( le ` U )


  assert |- ( ph -> .<_ C_ ( B X. B ) )

  proof
    wph
    c.le
    cF
    cR
    cple
    cfv
    #
    ccom
    #
    cF
    ccnv
    #
    ccom
    #
    cB
    cB
    cxp
    #
    wph
    cB
    cR
    cU
    cF
    c.le
    @0
    cV
    cZ
    imasless.u
    imasless.v
    imasless.f
    imasless.r
    @0
    eqid
    imasless.l
    imasle
    wph
    @3
    @3
    cdm
    #
    @3
    crn
    #
    cxp
    #
    @4
    @3
    wrel
    @3
    @7
    wss
    @1
    @2
    relco
    @3
    relssdmrn
    ax-mp
    wph
    @5
    cB
    wss
    @6
    cB
    wss
    @7
    @4
    wss
    wph
    @5
    @2
    ccnv
    #
    @1
    cdm
    #
    cima
    #
    cB
    @1
    @2
    dmco
    wph
    @10
    cF
    @9
    cima
    #
    cB
    wph
    @8
    cF
    @9
    wph
    cF
    wrel
    #
    @8
    cF
    wceq
    wph
    cV
    cB
    cF
    wfo
    #
    cV
    cB
    cF
    wf
    @12
    imasless.f
    cV
    cB
    cF
    fof
    cV
    cB
    cF
    frel
    3syl
    cF
    dfrel2
    sylib
    imaeq1d
    wph
    cF
    crn
    #
    @11
    cB
    cF
    @9
    imassrn
    wph
    @13
    @14
    cB
    wceq
    imasless.f
    cV
    cB
    cF
    forn
    syl
    #
    syl5sseq
    eqsstrd
    syl5eqss
    wph
    @6
    @1
    crn
    #
    cB
    @1
    @2
    rncoss
    wph
    @16
    cF
    @0
    crn
    #
    cima
    #
    cB
    cF
    @0
    rnco2
    wph
    @14
    @18
    cB
    cF
    @17
    imassrn
    @15
    syl5sseq
    syl5eqss
    syl5ss
    @5
    cB
    @6
    cB
    xpss12
    syl2anc
    syl5ss
    eqsstrd
end
