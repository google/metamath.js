include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cop.mm"
include "wf1.mm"
include "wf.mm"
include "jca.mm"
include "f1sng.mm"
include "f1f.mm"
include "3syl.mm"

theorem fsnd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume fsnd.a: |- ( ph -> A e. V )
  assume fsnd.b: |- ( ph -> B e. W )


  assert |- ( ph -> { <. A , B >. } : { A } --> W )

  proof
    wph
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    cA
    csn
    #
    cW
    cA
    cB
    cop
    csn
    #
    wf1
    @2
    cW
    @3
    wf
    wph
    @0
    @1
    fsnd.a
    fsnd.b
    jca
    cA
    cB
    cV
    cW
    f1sng
    @2
    cW
    @3
    f1f
    3syl
end
