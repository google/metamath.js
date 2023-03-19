include "c1.mm"
include "c3.mm"
include "1re.mm"
include "3re.mm"
include "1lt3.mm"
include "ltleii.mm"

theorem 1le3



  assert |- 1 <_ 3

  proof
    c1
    c3
    1re
    3re
    1lt3
    ltleii
end
