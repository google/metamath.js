include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "ccsh.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cmin.mm"
include "wceq.mm"
include "2cshwid.mm"
include "3adant2.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "cshwcl.mm"
include "3ad2ant1.mm"
include "lencl.mm"
include "nn0zd.mm"
include "zsubcl.mm"
include "sylan.mm"
include "simp2.mm"
include "2cshwcom.mm"
include "syl3anc.mm"
include "eqtrd.mm"

theorem 3cshw
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ZZ /\ M e. ZZ ) -> ( W cyclShift N ) = ( ( ( W cyclShift M ) cyclShift N ) cyclShift ( ( # ` W ) - M ) ) )

  proof
    cW
    cV
    cword
    #
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
    cW
    cN
    ccsh
    co
    cW
    cM
    ccsh
    co
    #
    cW
    chash
    cfv
    #
    cM
    cmin
    co
    #
    ccsh
    co
    #
    cN
    ccsh
    co
    #
    @5
    cN
    ccsh
    co
    @7
    ccsh
    co
    #
    @4
    cW
    @8
    cN
    ccsh
    @4
    @8
    cW
    @1
    @3
    @8
    cW
    wceq
    @2
    cM
    cV
    cW
    2cshwid
    3adant2
    eqcomd
    oveq1d
    @4
    @5
    @0
    wcel
    #
    @7
    cz
    wcel
    #
    @2
    @9
    @10
    wceq
    @1
    @2
    @11
    @3
    cM
    cV
    cW
    cshwcl
    3ad2ant1
    @1
    @3
    @12
    @2
    @1
    @6
    cz
    wcel
    @3
    @12
    @1
    @6
    cV
    cW
    lencl
    nn0zd
    @6
    cM
    zsubcl
    sylan
    3adant2
    @1
    @2
    @3
    simp2
    cN
    @7
    cV
    @5
    2cshwcom
    syl3anc
    eqtrd
end
