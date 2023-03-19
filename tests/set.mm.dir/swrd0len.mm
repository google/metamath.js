include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cop.mm"
include "csubstr.mm"
include "cfzo.mm"
include "cres.mm"
include "swrd0val.mm"
include "fveq2d.mm"
include "wfn.mm"
include "wceq.mm"
include "wss.mm"
include "wrdfn.mm"
include "cuz.mm"
include "elfzuz3.mm"
include "fzoss2.mm"
include "syl.mm"
include "fnssres.mm"
include "syl2an.mm"
include "hashfn.mm"
include "cn0.mm"
include "elfznn0.mm"
include "adantl.mm"
include "hashfzo0.mm"
include "3eqtrd.mm"

theorem swrd0len
  let cA: class A
  let cS: class S
  let cL: class L
  let vb: setvar b
  let vs: setvar s
  let vx: setvar x
  let cF: class F
  let cV: class V
  let cX: class X


  assert |- ( ( S e. Word A /\ L e. ( 0 ... ( # ` S ) ) ) -> ( # ` ( S substr <. 0 , L >. ) ) = L )

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
    cc0
    cL
    cop
    csubstr
    co
    #
    chash
    cfv
    cS
    cc0
    cL
    cfzo
    co
    #
    cres
    #
    chash
    cfv
    #
    @5
    chash
    cfv
    #
    cL
    @3
    @4
    @6
    chash
    cA
    cS
    cL
    swrd0val
    fveq2d
    @3
    @6
    @5
    wfn
    #
    @7
    @8
    wceq
    @0
    cS
    cc0
    @1
    cfzo
    co
    #
    wfn
    @5
    @10
    wss
    #
    @9
    @2
    cA
    cS
    wrdfn
    @2
    @1
    cL
    cuz
    cfv
    wcel
    @11
    cL
    cc0
    @1
    elfzuz3
    cL
    cc0
    @1
    fzoss2
    syl
    @10
    @5
    cS
    fnssres
    syl2an
    @5
    @6
    hashfn
    syl
    @3
    cL
    cn0
    wcel
    #
    @8
    cL
    wceq
    @2
    @12
    @0
    cL
    @1
    elfznn0
    adantl
    cL
    hashfzo0
    syl
    3eqtrd
end
