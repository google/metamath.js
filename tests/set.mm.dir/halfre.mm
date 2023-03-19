include "c2.mm"
include "2re.mm"
include "2ne0.mm"
include "rereccli.mm"

theorem halfre



  assert |- ( 1 / 2 ) e. RR

  proof
    c2
    2re
    2ne0
    rereccli
end
