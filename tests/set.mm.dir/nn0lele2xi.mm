include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "nn0le2xi.mm"
include "nn0rei.mm"
include "2re.mm"
include "remulcli.mm"
include "letri.mm"
include "mpan2.mm"

theorem nn0lele2xi
  let cM: class M
  let cN: class N
  assume nn0lele2xi.1: |- M e. NN0
  assume nn0lele2xi.2: |- N e. NN0


  assert |- ( N <_ M -> N <_ ( 2 x. M ) )

  proof
    cN
    cM
    cle
    wbr
    cM
    c2
    cM
    cmul
    co
    #
    cle
    wbr
    cN
    @0
    cle
    wbr
    cM
    nn0lele2xi.1
    nn0le2xi
    cN
    cM
    @0
    cN
    nn0lele2xi.2
    nn0rei
    cM
    nn0lele2xi.1
    nn0rei
    #
    c2
    cM
    2re
    @1
    remulcli
    letri
    mpan2
end
