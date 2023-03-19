include "wn.mm"
include "exmid.mm"

theorem testable
  let wph: wff ph
  let vk: setvar k
  let vx: setvar x


  assert |- ( -. ph \/ -. -. ph )

  proof
    wph
    wn
    exmid
end
