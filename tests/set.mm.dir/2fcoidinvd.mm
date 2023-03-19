include "fcof1od.mm"
include "fcof1oinvd.mm"

theorem 2fcoidinvd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  assume fcof1od.f: |- ( ph -> F : A --> B )
  assume fcof1od.g: |- ( ph -> G : B --> A )
  assume fcof1od.a: |- ( ph -> ( G o. F ) = ( _I |` A ) )
  assume fcof1od.b: |- ( ph -> ( F o. G ) = ( _I |` B ) )


  assert |- ( ph -> `' F = G )

  proof
    wph
    cA
    cB
    cF
    cG
    wph
    cA
    cB
    cF
    cG
    fcof1od.f
    fcof1od.g
    fcof1od.a
    fcof1od.b
    fcof1od
    fcof1od.g
    fcof1od.b
    fcof1oinvd
end
