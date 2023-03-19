include "cs1.mm"
include "c1.mm"
include "cclwwlkn.mm"
include "co.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cvtx.mm"
include "cword.mm"
include "cc0.mm"
include "csn.mm"
include "cedg.mm"
include "w3a.mm"
include "clwwlkn1.mm"
include "wi.mm"
include "s1fv.mm"
include "sneqd.mm"
include "eleq1d.mm"
include "biimpcd.mm"
include "3ad2ant3.mm"
include "com12.mm"
include "wa.mm"
include "s1len.mm"
include "a1i.mm"
include "s1cl.mm"
include "adantr.mm"
include "eqcomd.mm"
include "biimpa.mm"
include "3jca.mm"
include "ex.mm"
include "impbid.mm"
include "syl5rbb.mm"

theorem loopclwwlkn1b
  let cG: class G
  let cV: class V


  assert |- ( V e. ( Vtx ` G ) -> ( { V } e. ( Edg ` G ) <-> <" V "> e. ( 1 ClWWalksN G ) ) )

  proof
    cV
    cs1
    #
    c1
    cG
    cclwwlkn
    co
    wcel
    @0
    chash
    cfv
    c1
    wceq
    #
    @0
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    cc0
    @0
    cfv
    #
    csn
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    w3a
    #
    cV
    @2
    wcel
    #
    cV
    csn
    #
    @6
    wcel
    #
    cG
    @0
    clwwlkn1
    @9
    @8
    @11
    @8
    @9
    @11
    @7
    @1
    @9
    @11
    wi
    @3
    @9
    @7
    @11
    @9
    @5
    @10
    @6
    @9
    @4
    cV
    cV
    @2
    s1fv
    #
    sneqd
    eleq1d
    biimpcd
    3ad2ant3
    com12
    @9
    @11
    @8
    @9
    @11
    wa
    #
    @1
    @3
    @7
    @1
    @13
    cV
    s1len
    a1i
    @9
    @3
    @11
    cV
    @2
    s1cl
    adantr
    @9
    @11
    @7
    @9
    @10
    @5
    @6
    @9
    cV
    @4
    @9
    @4
    cV
    @12
    eqcomd
    sneqd
    eleq1d
    biimpa
    3jca
    ex
    impbid
    syl5rbb
end
