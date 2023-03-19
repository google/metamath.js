include "wnfc.mm"
include "wb.mm"
include "wa.mm"
include "nfnfc1.mm"
include "nfan.mm"
include "nfceqdf.mm"
include "syl2anc.mm"
include "mpbii.mm"

theorem nfded2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume nfded2.1: |- ( ph -> F/_ x A )
  assume nfded2.2: |- ( ph -> F/_ x B )
  assume nfded2.3: |- ( ( F/_ x A /\ F/_ x B ) -> C = D )
  assume nfded2.4: |- F/_ x C


  assert |- ( ph -> F/_ x D )

  proof
    wph
    vx
    cC
    wnfc
    #
    vx
    cD
    wnfc
    #
    nfded2.4
    wph
    vx
    cA
    wnfc
    #
    vx
    cB
    wnfc
    #
    @0
    @1
    wb
    nfded2.1
    nfded2.2
    @2
    @3
    wa
    vx
    cC
    cD
    @2
    @3
    vx
    vx
    cA
    nfnfc1
    vx
    cB
    nfnfc1
    nfan
    nfded2.3
    nfceqdf
    syl2anc
    mpbii
end
