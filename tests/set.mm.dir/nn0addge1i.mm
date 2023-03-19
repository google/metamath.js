include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "nn0addge1.mm"
include "mp2an.mm"

theorem nn0addge1i
  let cA: class A
  let cN: class N
  assume nn0addge1i.1: |- A e. RR
  assume nn0addge1i.2: |- N e. NN0


  assert |- A <_ ( A + N )

  proof
    cA
    cr
    wcel
    cN
    cn0
    wcel
    cA
    cA
    cN
    caddc
    co
    cle
    wbr
    nn0addge1i.1
    nn0addge1i.2
    cA
    cN
    nn0addge1
    mp2an
end
