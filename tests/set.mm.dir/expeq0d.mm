include "cexp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cc.mm"
include "wcel.mm"
include "cn.mm"
include "wb.mm"
include "expeq0.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem expeq0d
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume expcld.1: |- ( ph -> A e. CC )
  assume expeq0d.2: |- ( ph -> N e. NN )
  assume expeq0d.3: |- ( ph -> ( A ^ N ) = 0 )


  assert |- ( ph -> A = 0 )

  proof
    wph
    cA
    cN
    cexp
    co
    cc0
    wceq
    #
    cA
    cc0
    wceq
    #
    expeq0d.3
    wph
    cA
    cc
    wcel
    cN
    cn
    wcel
    @0
    @1
    wb
    expcld.1
    expeq0d.2
    cA
    cN
    expeq0
    syl2anc
    mpbid
end
