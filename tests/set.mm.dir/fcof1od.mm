include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "wf.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "fcof1.mm"
include "syl2anc.mm"
include "fcofo.mm"
include "syl3anc.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem fcof1od
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  assume fcof1od.f: |- ( ph -> F : A --> B )
  assume fcof1od.g: |- ( ph -> G : B --> A )
  assume fcof1od.a: |- ( ph -> ( G o. F ) = ( _I |` A ) )
  assume fcof1od.b: |- ( ph -> ( F o. G ) = ( _I |` B ) )


  assert |- ( ph -> F : A -1-1-onto-> B )

  proof
    wph
    cA
    cB
    cF
    wf1
    #
    cA
    cB
    cF
    wfo
    #
    cA
    cB
    cF
    wf1o
    wph
    cA
    cB
    cF
    wf
    #
    cG
    cF
    ccom
    cid
    cA
    cres
    wceq
    @0
    fcof1od.f
    fcof1od.a
    cA
    cB
    cG
    cF
    fcof1
    syl2anc
    wph
    @2
    cB
    cA
    cG
    wf
    cF
    cG
    ccom
    cid
    cB
    cres
    wceq
    @1
    fcof1od.f
    fcof1od.g
    fcof1od.b
    cA
    cB
    cG
    cF
    fcofo
    syl3anc
    cA
    cB
    cF
    df-f1o
    sylanbrc
end
