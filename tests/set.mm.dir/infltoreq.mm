include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "ccnv.mm"
include "wor.mm"
include "cnvso.mm"
include "sylib.mm"
include "cinf.mm"
include "csup.mm"
include "df-inf.mm"
include "syl6eq.mm"
include "supgtoreq.mm"
include "wcel.mm"
include "wb.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "ne0i.mm"
include "syl.mm"
include "fiinfcl.mm"
include "syl13anc.mm"
include "eqeltrd.mm"
include "wa.mm"
include "brcnvg.mm"
include "bicomd.mm"
include "syl2anc.mm"
include "orbi1d.mm"
include "mpbird.mm"

theorem infltoreq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  assume infltoreq.1: |- ( ph -> R Or A )
  assume infltoreq.2: |- ( ph -> B C_ A )
  assume infltoreq.3: |- ( ph -> B e. Fin )
  assume infltoreq.4: |- ( ph -> C e. B )
  assume infltoreq.5: |- ( ph -> S = inf ( B , A , R ) )


  assert |- ( ph -> ( S R C \/ C = S ) )

  proof
    wph
    cS
    cC
    cR
    wbr
    #
    cC
    cS
    wceq
    #
    wo
    cC
    cS
    cR
    ccnv
    #
    wbr
    #
    @1
    wo
    wph
    cA
    cB
    cC
    @2
    cS
    wph
    cA
    cR
    wor
    #
    cA
    @2
    wor
    infltoreq.1
    cA
    cR
    cnvso
    sylib
    infltoreq.2
    infltoreq.3
    infltoreq.4
    wph
    cS
    cB
    cA
    cR
    cinf
    #
    cB
    cA
    @2
    csup
    infltoreq.5
    cB
    cA
    cR
    df-inf
    syl6eq
    supgtoreq
    wph
    @0
    @3
    @1
    wph
    cC
    cB
    wcel
    #
    cS
    cB
    wcel
    #
    @0
    @3
    wb
    infltoreq.4
    wph
    cS
    @5
    cB
    infltoreq.5
    wph
    @4
    cB
    cfn
    wcel
    cB
    c0
    wne
    #
    cB
    cA
    wss
    @5
    cB
    wcel
    infltoreq.1
    infltoreq.3
    wph
    @6
    @8
    infltoreq.4
    cB
    cC
    ne0i
    syl
    infltoreq.2
    cA
    cB
    cR
    fiinfcl
    syl13anc
    eqeltrd
    @6
    @7
    wa
    @3
    @0
    cC
    cS
    cB
    cB
    cR
    brcnvg
    bicomd
    syl2anc
    orbi1d
    mpbird
end
