include "cword.mm"
include "wcel.mm"
include "cn.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cpfx.mm"
include "co.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "c0.mm"
include "cn0.mm"
include "wa.mm"
include "wceq.mm"
include "nnnn0.mm"
include "anim2i.mm"
include "3adant3.mm"
include "pfxval.mm"
include "syl.mm"
include "swrdn0.mm"
include "eqnetrd.mm"

theorem pfxn0
  let cL: class L
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ L e. NN /\ L <_ ( # ` W ) ) -> ( W prefix L ) =/= (/) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cL
    cn
    wcel
    #
    cL
    cW
    chash
    cfv
    cle
    wbr
    #
    w3a
    #
    cW
    cL
    cpfx
    co
    #
    cW
    cc0
    cL
    cop
    csubstr
    co
    #
    c0
    @4
    @1
    cL
    cn0
    wcel
    #
    wa
    #
    @5
    @6
    wceq
    @1
    @2
    @8
    @3
    @2
    @7
    @1
    cL
    nnnn0
    anim2i
    3adant3
    cW
    cL
    @0
    pfxval
    syl
    cL
    cV
    cW
    swrdn0
    eqnetrd
end
