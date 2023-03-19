include "wnfc.mm"
include "wb.mm"
include "nfnfc1.mm"
include "nfceqdf.mm"
include "syl.mm"
include "mpbii.mm"

theorem nfded
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume nfded.1: |- ( ph -> F/_ x A )
  assume nfded.2: |- ( F/_ x A -> B = C )
  assume nfded.3: |- F/_ x B


  assert |- ( ph -> F/_ x C )

  proof
    wph
    vx
    cB
    wnfc
    #
    vx
    cC
    wnfc
    #
    nfded.3
    wph
    vx
    cA
    wnfc
    #
    @0
    @1
    wb
    nfded.1
    @2
    vx
    cB
    cC
    vx
    cA
    nfnfc1
    nfded.2
    nfceqdf
    syl
    mpbii
end
