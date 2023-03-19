include "cword.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cz.mm"
include "w3a.mm"
include "cc0.mm"
include "ccsh.mm"
include "co.mm"
include "cfv.mm"
include "caddc.mm"
include "chash.mm"
include "cmo.mm"
include "cfzo.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3.mm"
include "wa.mm"
include "cn.mm"
include "lennncl.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "3adant3.mm"
include "cshwidxmod.mm"
include "syl3anc.mm"
include "zcn.mm"
include "addid2d.mm"
include "3ad2ant3.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem cshwidx0mod
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ W =/= (/) /\ N e. ZZ ) -> ( ( W cyclShift N ) ` 0 ) = ( W ` ( N mod ( # ` W ) ) ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cW
    c0
    wne
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cc0
    cW
    cN
    ccsh
    co
    cfv
    #
    cc0
    cN
    caddc
    co
    #
    cW
    chash
    cfv
    #
    cmo
    co
    #
    cW
    cfv
    #
    cN
    @6
    cmo
    co
    #
    cW
    cfv
    @3
    @0
    @2
    cc0
    cc0
    @6
    cfzo
    co
    wcel
    #
    @4
    @8
    wceq
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp3
    @0
    @1
    @10
    @2
    @0
    @1
    wa
    @6
    cn
    wcel
    @10
    cV
    cW
    lennncl
    @6
    lbfzo0
    sylibr
    3adant3
    cc0
    cN
    cV
    cW
    cshwidxmod
    syl3anc
    @3
    @7
    @9
    cW
    @3
    @5
    cN
    @6
    cmo
    @2
    @0
    @5
    cN
    wceq
    @1
    @2
    cN
    cN
    zcn
    addid2d
    3ad2ant3
    oveq1d
    fveq2d
    eqtrd
end
