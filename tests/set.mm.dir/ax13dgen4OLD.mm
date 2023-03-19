include "ax13dgen1.mm"

theorem ax13dgen4OLD
  let vx: setvar x


  assert |- ( -. x = x -> ( x = x -> A. x x = x ) )

  proof
    vx
    vx
    ax13dgen1
end
