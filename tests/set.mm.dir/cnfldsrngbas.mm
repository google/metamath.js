include "cc.mm"
include "ccnfld.mm"
include "cnfldbas.mm"
include "ressbas2.mm"

theorem cnfldsrngbas
  let cR: class R
  let cS: class S
  let vk: setvar k
  let vx: setvar x
  assume cnfldsrngbas.r: |- R = ( CCfld |`s S )


  assert |- ( S C_ CC -> S = ( Base ` R ) )

  proof
    cS
    cc
    cR
    ccnfld
    cnfldsrngbas.r
    cnfldbas
    ressbas2
end
