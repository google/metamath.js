include "cn0.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "nn0addcl.mm"
include "mp2an.mm"

theorem nn0addcli
  let cM: class M
  let cN: class N
  assume nn0addcli.1: |- M e. NN0
  assume nn0addcli.2: |- N e. NN0


  assert |- ( M + N ) e. NN0

  proof
    cM
    cn0
    wcel
    cN
    cn0
    wcel
    cM
    cN
    caddc
    co
    cn0
    wcel
    nn0addcli.1
    nn0addcli.2
    cM
    cN
    nn0addcl
    mp2an
end
