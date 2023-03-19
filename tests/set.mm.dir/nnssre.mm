include "c1.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wral.mm"
include "cn.mm"
include "wss.mm"
include "1re.mm"
include "peano2re.mm"
include "rgen.mm"
include "peano5nni.mm"
include "mp2an.mm"

theorem nnssre
  let vx: setvar x


  assert |- NN C_ RR

  proof
    c1
    cr
    wcel
    vx
    cv
    #
    c1
    caddc
    co
    cr
    wcel
    #
    vx
    cr
    wral
    cn
    cr
    wss
    1re
    @1
    vx
    cr
    @0
    peano2re
    rgen
    vx
    cr
    peano5nni
    mp2an
end
