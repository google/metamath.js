include "caddc.mm"
include "ccnfld.mm"
include "cnfldadd.mm"
include "ressplusg.mm"

theorem cnfldsrngadd
  let cR: class R
  let cS: class S
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume cnfldsrngbas.r: |- R = ( CCfld |`s S )


  assert |- ( S e. V -> + = ( +g ` R ) )

  proof
    cS
    caddc
    ccnfld
    cR
    cV
    cnfldsrngbas.r
    cnfldadd
    ressplusg
end
