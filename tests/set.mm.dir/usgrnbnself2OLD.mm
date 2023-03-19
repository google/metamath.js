include "cusgr.mm"
include "nbgrnself2OLD.mm"

theorem usgrnbnself2OLD
  let cG: class G
  let cN: class N


  assert |- ( G e. USGraph -> N e/ ( G NeighbVtx N ) )

  proof
    cG
    cN
    cusgr
    nbgrnself2OLD
end
