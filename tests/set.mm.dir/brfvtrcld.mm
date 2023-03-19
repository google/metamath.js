include "ctcl.mm"
include "cn.mm"
include "dftrcl3.mm"
include "cn0.mm"
include "wss.mm"
include "nnssnn0.mm"
include "a1i.mm"
include "brmptiunrelexpd.mm"

theorem brfvtrcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let vn: setvar n
  let vr: setvar r
  assume brfvtrcld.r: |- ( ph -> R e. _V )

  disjoint A n
  disjoint B n
  disjoint R n
  disjoint n r
  disjoint R r
  assert |- ( ph -> ( A ( t+ ` R ) B <-> E. n e. NN A ( R ^r n ) B ) )

  proof
    wph
    cA
    cB
    ctcl
    cR
    vn
    cn
    vr
    vn
    vr
    dftrcl3
    brfvtrcld.r
    cn
    cn0
    wss
    wph
    nnssnn0
    a1i
    brmptiunrelexpd
end
