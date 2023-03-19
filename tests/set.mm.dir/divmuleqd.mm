include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "wb.mm"
include "jca.mm"
include "divmuleq.mm"
include "syl22anc.mm"

theorem divmuleqd
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


  assert |- ( ph -> ( ( A / B ) = ( C / D ) <-> ( A x. D ) = ( C x. B ) ) )

  proof
    wph
    cA
    cc
    wcel
    cC
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
    wceq
    cA
    cD
    cmul
    co
    cC
    cB
    cmul
    co
    wceq
    wb
    div1d.1
    divmuld.3
    wph
    @0
    @1
    divcld.2
    divmuldivd.5
    jca
    wph
    @2
    @3
    divmuldivd.4
    divmuldivd.6
    jca
    cA
    cC
    cB
    cD
    divmuleq
    syl22anc
end
