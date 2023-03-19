include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "0exp.mm"
include "syl.mm"

theorem 0expd
  let wph: wff ph
  let cN: class N
  assume 0exp.1: |- ( ph -> N e. NN )


  assert |- ( ph -> ( 0 ^ N ) = 0 )

  proof
    wph
    cN
    cn
    wcel
    cc0
    cN
    cexp
    co
    cc0
    wceq
    0exp.1
    cN
    0exp
    syl
end
