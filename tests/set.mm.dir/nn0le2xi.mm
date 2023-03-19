include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "cle.mm"
include "nn0rei.mm"
include "nn0addge1i.mm"
include "nn0cni.mm"
include "2timesi.mm"
include "breqtrri.mm"

theorem nn0le2xi
  let cN: class N
  assume nn0le2xi.1: |- N e. NN0


  assert |- N <_ ( 2 x. N )

  proof
    cN
    cN
    cN
    caddc
    co
    c2
    cN
    cmul
    co
    cle
    cN
    cN
    cN
    nn0le2xi.1
    nn0rei
    nn0le2xi.1
    nn0addge1i
    cN
    cN
    nn0le2xi.1
    nn0cni
    2timesi
    breqtrri
end
