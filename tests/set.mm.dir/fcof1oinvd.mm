include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "coeq2d.mm"
include "coass.mm"
include "wf1o.mm"
include "wceq.mm"
include "f1ococnv1.mm"
include "syl.mm"
include "coeq1d.mm"
include "wf.mm"
include "fcoi2.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "fcoi1.mm"
include "3eqtr3rd.mm"

theorem fcof1oinvd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  assume fcof1oinvd.f: |- ( ph -> F : A -1-1-onto-> B )
  assume fcof1oinvd.g: |- ( ph -> G : B --> A )
  assume fcof1oinvd.b: |- ( ph -> ( F o. G ) = ( _I |` B ) )


  assert |- ( ph -> `' F = G )

  proof
    wph
    cF
    ccnv
    #
    cF
    cG
    ccom
    #
    ccom
    #
    @0
    cid
    cB
    cres
    #
    ccom
    #
    cG
    @0
    wph
    @1
    @3
    @0
    fcof1oinvd.b
    coeq2d
    wph
    @2
    @0
    cF
    ccom
    #
    cG
    ccom
    #
    cG
    @0
    cF
    cG
    coass
    wph
    @6
    cid
    cA
    cres
    #
    cG
    ccom
    #
    cG
    wph
    @5
    @7
    cG
    wph
    cA
    cB
    cF
    wf1o
    #
    @5
    @7
    wceq
    fcof1oinvd.f
    cA
    cB
    cF
    f1ococnv1
    syl
    coeq1d
    wph
    cB
    cA
    cG
    wf
    @8
    cG
    wceq
    fcof1oinvd.g
    cB
    cA
    cG
    fcoi2
    syl
    eqtrd
    syl5eqr
    wph
    cB
    cA
    @0
    wf
    #
    @4
    @0
    wceq
    wph
    cB
    cA
    @0
    wf1o
    #
    @10
    wph
    @9
    @11
    fcof1oinvd.f
    cA
    cB
    cF
    f1ocnv
    syl
    cB
    cA
    @0
    f1of
    syl
    cB
    cA
    @0
    fcoi1
    syl
    3eqtr3rd
end
