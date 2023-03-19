include "cn0.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "simpl.mm"
include "eluznn0.mm"
include "eluzle.mm"
include "adantl.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "fznn0sub2.mm"
include "syl.mm"

theorem uzsubfz0
  let cL: class L
  let cN: class N


  assert |- ( ( L e. NN0 /\ N e. ( ZZ>= ` L ) ) -> ( N - L ) e. ( 0 ... N ) )

  proof
    cL
    cn0
    wcel
    #
    cN
    cL
    cuz
    cfv
    wcel
    #
    wa
    #
    cL
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    cN
    cL
    cmin
    co
    @3
    wcel
    @2
    @0
    cN
    cn0
    wcel
    cL
    cN
    cle
    wbr
    #
    @4
    @0
    @1
    simpl
    cN
    cL
    eluznn0
    @1
    @5
    @0
    cL
    cN
    eluzle
    adantl
    cL
    cN
    elfz2nn0
    syl3anbrc
    cL
    cN
    fznn0sub2
    syl
end
