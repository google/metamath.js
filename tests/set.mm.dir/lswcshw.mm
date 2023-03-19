include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "ccsh.mm"
include "clsw.mm"
include "cmin.mm"
include "cvv.mm"
include "wceq.mm"
include "ovex.mm"
include "lsw.mm"
include "mp1i.mm"
include "cz.mm"
include "elfzelz.mm"
include "cshwlen.mm"
include "sylan2.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "cshwidxn.mm"
include "3eqtrd.mm"

theorem lswcshw
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ( 1 ... ( # ` W ) ) ) -> ( lastS ` ( W cyclShift N ) ) = ( W ` ( N - 1 ) ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cN
    c1
    cW
    chash
    cfv
    #
    cfz
    co
    wcel
    #
    wa
    #
    cW
    cN
    ccsh
    co
    #
    clsw
    cfv
    #
    @4
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @4
    cfv
    #
    @1
    c1
    cmin
    co
    #
    @4
    cfv
    cN
    c1
    cmin
    co
    cW
    cfv
    @4
    cvv
    wcel
    @5
    @8
    wceq
    @3
    cW
    cN
    ccsh
    ovex
    @4
    cvv
    lsw
    mp1i
    @3
    @7
    @9
    @4
    @3
    @6
    @1
    c1
    cmin
    @2
    @0
    cN
    cz
    wcel
    @6
    @1
    wceq
    cN
    c1
    @1
    elfzelz
    cN
    cV
    cW
    cshwlen
    sylan2
    oveq1d
    fveq2d
    cN
    cV
    cW
    cshwidxn
    3eqtrd
end
