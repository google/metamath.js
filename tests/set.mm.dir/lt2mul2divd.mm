include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wb.mm"
include "rpregt0d.mm"
include "lt2mul2div.mm"
include "syl22anc.mm"

theorem lt2mul2divd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume lt2mul2divd.1: |- ( ph -> A e. RR )
  assume lt2mul2divd.2: |- ( ph -> B e. RR+ )
  assume lt2mul2divd.3: |- ( ph -> C e. RR )
  assume lt2mul2divd.4: |- ( ph -> D e. RR+ )


  assert |- ( ph -> ( ( A x. B ) < ( C x. D ) <-> ( A / D ) < ( C / B ) ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cc0
    cB
    clt
    wbr
    wa
    cC
    cr
    wcel
    cD
    cr
    wcel
    cc0
    cD
    clt
    wbr
    wa
    cA
    cB
    cmul
    co
    cC
    cD
    cmul
    co
    clt
    wbr
    cA
    cD
    cdiv
    co
    cC
    cB
    cdiv
    co
    clt
    wbr
    wb
    lt2mul2divd.1
    wph
    cB
    lt2mul2divd.2
    rpregt0d
    lt2mul2divd.3
    wph
    cD
    lt2mul2divd.4
    rpregt0d
    cA
    cB
    cC
    cD
    lt2mul2div
    syl22anc
end
