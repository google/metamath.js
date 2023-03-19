include "c1.mm"
include "c2.mm"
include "1re.mm"
include "2re.mm"
include "1lt2.mm"
include "ltleii.mm"

theorem 1le2



  assert |- 1 <_ 2

  proof
    c1
    c2
    1re
    2re
    1lt2
    ltleii
end
