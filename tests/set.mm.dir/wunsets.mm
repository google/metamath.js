include "csts.mm"
include "co.mm"
include "cvv.mm"
include "csn.mm"
include "cdm.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "wcel.mm"
include "wceq.mm"
include "setsvalg.mm"
include "syl2anc.mm"
include "wunres.mm"
include "wunsn.mm"
include "wunun.mm"
include "eqeltrd.mm"

theorem wunsets
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cU: class U
  assume wunsets.1: |- ( ph -> U e. WUni )
  assume wunsets.2: |- ( ph -> S e. U )
  assume wunsets.3: |- ( ph -> A e. U )


  assert |- ( ph -> ( S sSet A ) e. U )

  proof
    wph
    cS
    cA
    csts
    co
    #
    cS
    cvv
    cA
    csn
    #
    cdm
    cdif
    #
    cres
    #
    @1
    cun
    #
    cU
    wph
    cS
    cU
    wcel
    cA
    cU
    wcel
    @0
    @4
    wceq
    wunsets.2
    wunsets.3
    cA
    cS
    cU
    cU
    setsvalg
    syl2anc
    wph
    @3
    @1
    cU
    wunsets.1
    wph
    cS
    @2
    cU
    wunsets.1
    wunsets.2
    wunres
    wph
    cA
    cU
    wunsets.1
    wunsets.3
    wunsn
    wunun
    eqeltrd
end
