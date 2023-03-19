include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cpfx.mm"
include "cfzo.mm"
include "wfn.mm"
include "wceq.mm"
include "pfxfn.mm"
include "hashfn.mm"
include "syl.mm"
include "cn0.mm"
include "elfznn0.mm"
include "adantl.mm"
include "hashfzo0.mm"
include "eqtrd.mm"

theorem pfxlen
  let cA: class A
  let cS: class S
  let cL: class L
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( S e. Word A /\ L e. ( 0 ... ( # ` S ) ) ) -> ( # ` ( S prefix L ) ) = L )

  proof
    cS
    cA
    cword
    wcel
    #
    cL
    cc0
    cS
    chash
    cfv
    #
    cfz
    co
    wcel
    #
    wa
    #
    cS
    cL
    cpfx
    co
    #
    chash
    cfv
    #
    cc0
    cL
    cfzo
    co
    #
    chash
    cfv
    #
    cL
    @3
    @4
    @6
    wfn
    @5
    @7
    wceq
    cS
    cL
    cA
    pfxfn
    @6
    @4
    hashfn
    syl
    @3
    cL
    cn0
    wcel
    #
    @7
    cL
    wceq
    @2
    @8
    @0
    cL
    @1
    elfznn0
    adantl
    cL
    hashfzo0
    syl
    eqtrd
end
