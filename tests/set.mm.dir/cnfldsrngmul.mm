include "ccnfld.mm"
include "cmul.mm"
include "cnfldmul.mm"
include "ressmulr.mm"

theorem cnfldsrngmul
  let cR: class R
  let cS: class S
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume cnfldsrngbas.r: |- R = ( CCfld |`s S )


  assert |- ( S e. V -> x. = ( .r ` R ) )

  proof
    cS
    ccnfld
    cR
    cmul
    cV
    cnfldsrngbas.r
    cnfldmul
    ressmulr
end
