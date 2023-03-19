include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ctan.mm"
include "cfv.mm"
include "cdiv.mm"
include "csin.mm"
include "ccos.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "ax-icn.mm"
include "recn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "rpcoshcl.mm"
include "rpne0d.mm"
include "tanval.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "sincld.mm"
include "recoshcl.mm"
include "recnd.mm"
include "a1i.mm"
include "ine0.mm"
include "divdiv32d.mm"
include "eqtrd.mm"
include "resinhcl.mm"
include "rerpdivcld.mm"
include "eqeltrd.mm"

theorem retanhcl
  let cA: class A


  assert |- ( A e. RR -> ( ( tan ` ( _i x. A ) ) / _i ) e. RR )

  proof
    cA
    cr
    wcel
    #
    ci
    cA
    cmul
    co
    #
    ctan
    cfv
    #
    ci
    cdiv
    co
    #
    @1
    csin
    cfv
    #
    ci
    cdiv
    co
    #
    @1
    ccos
    cfv
    #
    cdiv
    co
    #
    cr
    @0
    @3
    @4
    @6
    cdiv
    co
    #
    ci
    cdiv
    co
    @7
    @0
    @2
    @8
    ci
    cdiv
    @0
    @1
    cc
    wcel
    #
    @6
    cc0
    wne
    @2
    @8
    wceq
    @0
    ci
    cc
    wcel
    #
    cA
    cc
    wcel
    @9
    ax-icn
    cA
    recn
    ci
    cA
    mulcl
    sylancr
    #
    @0
    @6
    cA
    rpcoshcl
    #
    rpne0d
    #
    @1
    tanval
    syl2anc
    oveq1d
    @0
    @4
    @6
    ci
    @0
    @1
    @11
    sincld
    @0
    @6
    cA
    recoshcl
    recnd
    @10
    @0
    ax-icn
    a1i
    @13
    ci
    cc0
    wne
    @0
    ine0
    a1i
    divdiv32d
    eqtrd
    @0
    @5
    @6
    cA
    resinhcl
    @12
    rerpdivcld
    eqeltrd
end
