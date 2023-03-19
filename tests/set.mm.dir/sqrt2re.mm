include "c2.mm"
include "2re.mm"
include "2pos.mm"
include "sqrtpclii.mm"

theorem sqrt2re



  assert |- ( sqrt ` 2 ) e. RR

  proof
    c2
    2re
    2pos
    sqrtpclii
end
