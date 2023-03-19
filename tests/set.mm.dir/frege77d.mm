include "ctcl.mm"
include "cfv.mm"
include "csn.mm"
include "cima.mm"
include "cvv.mm"
include "wcel.mm"
include "cun.mm"
include "wss.mm"
include "imaundi.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "trclimalb2.mm"
include "syl2anc.mm"
include "cop.mm"
include "wbr.mm"
include "df-br.mm"
include "sylib.mm"
include "wb.mm"
include "elimasng.mm"
include "mpbird.mm"
include "sseldd.mm"

theorem frege77d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  assume frege77d.r: |- ( ph -> R e. _V )
  assume frege77d.a: |- ( ph -> A e. _V )
  assume frege77d.b: |- ( ph -> B e. _V )
  assume frege77d.ab: |- ( ph -> A ( t+ ` R ) B )
  assume frege77d.he: |- ( ph -> ( R " U ) C_ U )
  assume frege77d.ss: |- ( ph -> ( R " { A } ) C_ U )


  assert |- ( ph -> B e. U )

  proof
    wph
    cR
    ctcl
    cfv
    #
    cA
    csn
    #
    cima
    #
    cU
    cB
    wph
    cR
    cvv
    wcel
    cR
    @1
    cU
    cun
    cima
    #
    cU
    wss
    @2
    cU
    wss
    frege77d.r
    wph
    @3
    cR
    @1
    cima
    #
    cR
    cU
    cima
    #
    cun
    cU
    cR
    @1
    cU
    imaundi
    wph
    @4
    @5
    cU
    frege77d.ss
    frege77d.he
    unssd
    syl5eqss
    @1
    cU
    cR
    cvv
    trclimalb2
    syl2anc
    wph
    cB
    @2
    wcel
    #
    cA
    cB
    cop
    @0
    wcel
    #
    wph
    cA
    cB
    @0
    wbr
    @7
    frege77d.ab
    cA
    cB
    @0
    df-br
    sylib
    wph
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    @6
    @7
    wb
    frege77d.a
    frege77d.b
    @0
    cA
    cB
    cvv
    cvv
    elimasng
    syl2anc
    mpbird
    sseldd
end
