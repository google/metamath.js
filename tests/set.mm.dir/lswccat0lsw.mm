include "cword.mm"
include "wcel.mm"
include "c0.mm"
include "cconcat.mm"
include "co.mm"
include "clsw.mm"
include "ccatrid.mm"
include "fveq2d.mm"

theorem lswccat0lsw
  let cV: class V
  let cW: class W


  assert |- ( W e. Word V -> ( lastS ` ( W ++ (/) ) ) = ( lastS ` W ) )

  proof
    cW
    cV
    cword
    wcel
    cW
    c0
    cconcat
    co
    cW
    clsw
    cV
    cW
    ccatrid
    fveq2d
end
