include "cstr.mm"
include "brstruct.mm"
include "brrelexi.mm"

theorem structex
  let cG: class G
  let cX: class X


  assert |- ( G Struct X -> G e. _V )

  proof
    cG
    cX
    cstr
    brstruct
    brrelexi
end
