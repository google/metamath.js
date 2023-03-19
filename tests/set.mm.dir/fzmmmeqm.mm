include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "cmin.mm"
include "wceq.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "elfz2.mm"
include "zcn.mm"
include "3anim123i.mm"
include "3comr.mm"
include "adantr.mm"
include "sylbi.mm"
include "nnncan2.mm"
include "syl.mm"

theorem fzmmmeqm
  let cL: class L
  let cM: class M
  let cN: class N


  assert |- ( M e. ( L ... N ) -> ( ( N - L ) - ( M - L ) ) = ( N - M ) )

  proof
    cM
    cL
    cN
    cfz
    co
    wcel
    #
    cN
    cc
    wcel
    #
    cM
    cc
    wcel
    #
    cL
    cc
    wcel
    #
    w3a
    #
    cN
    cL
    cmin
    co
    cM
    cL
    cmin
    co
    cmin
    co
    cN
    cM
    cmin
    co
    wceq
    @0
    cL
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    w3a
    #
    cL
    cM
    cle
    wbr
    cM
    cN
    cle
    wbr
    wa
    #
    wa
    @4
    cM
    cL
    cN
    elfz2
    @8
    @4
    @9
    @6
    @7
    @5
    @4
    @6
    @1
    @7
    @2
    @5
    @3
    cN
    zcn
    cM
    zcn
    cL
    zcn
    3anim123i
    3comr
    adantr
    sylbi
    cN
    cM
    cL
    nnncan2
    syl
end
