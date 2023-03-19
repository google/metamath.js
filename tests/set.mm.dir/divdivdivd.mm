include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "jca.mm"
include "divdivdiv.mm"
include "syl22anc.mm"

theorem divdivdivd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divmuld.3: |- ( ph -> C e. CC )
  assume divmuldivd.4: |- ( ph -> D e. CC )
  assume divmuldivd.5: |- ( ph -> B =/= 0 )
  assume divmuldivd.6: |- ( ph -> D =/= 0 )
  assume divdivdivd.7: |- ( ph -> C =/= 0 )


  assert |- ( ph -> ( ( A / B ) / ( C / D ) ) = ( ( A x. D ) / ( B x. C ) ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    wa
    cD
    cc
    wcel
    #
    cD
    cc0
    wne
    #
    wa
    cA
    cB
    cdiv
    co
    cC
    cD
    cdiv
    co
    cdiv
    co
    cA
    cD
    cmul
    co
    cB
    cC
    cmul
    co
    cdiv
    co
    wceq
    div1d.1
    wph
    @0
    @1
    divcld.2
    divmuldivd.5
    jca
    wph
    @2
    @3
    divmuld.3
    divdivdivd.7
    jca
    wph
    @4
    @5
    divmuldivd.4
    divmuldivd.6
    jca
    cA
    cB
    cC
    cD
    divdivdiv
    syl22anc
end
