include "cbs.mm"
include "c1.mm"
include "df-base.mm"
include "str0.mm"

theorem base0



  assert |- (/) = ( Base ` (/) )

  proof
    cbs
    c1
    df-base
    str0
end
