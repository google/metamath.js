include "c2.mm"
include "cn.mm"
include "wcel.mm"
include "2nn.mm"
include "a1i.mm"
include "expeq0d.mm"

theorem sqeq0d
  let wph: wff ph
  let cA: class A
  assume expcld.1: |- ( ph -> A e. CC )
  assume sqeq0d.1: |- ( ph -> ( A ^ 2 ) = 0 )


  assert |- ( ph -> A = 0 )

  proof
    wph
    cA
    c2
    expcld.1
    c2
    cn
    wcel
    wph
    2nn
    a1i
    sqeq0d.1
    expeq0d
end
