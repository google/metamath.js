include "c1.mm"
include "c4.mm"
include "c3.mm"
include "cmin.mm"
include "co.mm"
include "4re.mm"
include "recni.mm"
include "3re.mm"
include "1re.mm"
include "caddc.mm"
include "df-4.mm"
include "eqcomi.mm"
include "subaddrii.mm"
include "addcomi.mm"
include "eqtri.mm"

theorem problem3
  let cA: class A
  assume problem3.1: |- A e. CC
  assume problem3.2: |- ( A + 3 ) = 4


  assert |- A = 1

  proof
    c1
    cA
    c1
    c4
    c3
    cmin
    co
    #
    cA
    @0
    c1
    c4
    c3
    c1
    c4
    4re
    recni
    #
    c3
    3re
    recni
    #
    c1
    1re
    recni
    c4
    c3
    c1
    caddc
    co
    df-4
    eqcomi
    subaddrii
    eqcomi
    c4
    c3
    cA
    @1
    @2
    problem3.1
    c3
    cA
    caddc
    co
    cA
    c3
    caddc
    co
    c4
    c3
    cA
    @2
    problem3.1
    addcomi
    problem3.2
    eqtri
    subaddrii
    eqtri
    eqcomi
end
