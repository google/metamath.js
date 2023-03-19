include "wcel.mm"
include "cvv.mm"
include "elex.mm"
include "syl.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "snssd.mm"
include "imass2.mm"
include "sstrd.mm"
include "frege77d.mm"

theorem frege81d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  assume frege81d.r: |- ( ph -> R e. _V )
  assume frege81d.a: |- ( ph -> A e. U )
  assume frege81d.b: |- ( ph -> B e. _V )
  assume frege81d.ab: |- ( ph -> A ( t+ ` R ) B )
  assume frege81d.he: |- ( ph -> ( R " U ) C_ U )


  assert |- ( ph -> B e. U )

  proof
    wph
    cA
    cB
    cR
    cU
    frege81d.r
    wph
    cA
    cU
    wcel
    cA
    cvv
    wcel
    frege81d.a
    cA
    cU
    elex
    syl
    frege81d.b
    frege81d.ab
    frege81d.he
    wph
    cR
    cA
    csn
    #
    cima
    #
    cR
    cU
    cima
    #
    cU
    wph
    @0
    cU
    wss
    @1
    @2
    wss
    wph
    cA
    cU
    frege81d.a
    snssd
    @0
    cU
    cR
    imass2
    syl
    frege81d.he
    sstrd
    frege77d
end
