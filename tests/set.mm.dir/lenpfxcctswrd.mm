include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cpfx.mm"
include "cop.mm"
include "csubstr.mm"
include "cconcat.mm"
include "pfxcctswrd.mm"
include "fveq2d.mm"

theorem lenpfxcctswrd
  let cM: class M
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ M e. ( 0 ... ( # ` W ) ) ) -> ( # ` ( ( W prefix M ) ++ ( W substr <. M , ( # ` W ) >. ) ) ) = ( # ` W ) )

  proof
    cW
    cV
    cword
    wcel
    cM
    cc0
    cW
    chash
    cfv
    #
    cfz
    co
    wcel
    wa
    cW
    cM
    cpfx
    co
    cW
    cM
    @0
    cop
    csubstr
    co
    cconcat
    co
    cW
    chash
    cM
    cV
    cW
    pfxcctswrd
    fveq2d
end
