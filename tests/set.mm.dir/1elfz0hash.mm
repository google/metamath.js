include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "cn0.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "1nn0.mm"
include "a1i.mm"
include "hashcl.mm"
include "adantr.mm"
include "hashge1.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"

theorem 1elfz0hash
  let cA: class A


  assert |- ( ( A e. Fin /\ A =/= (/) ) -> 1 e. ( 0 ... ( # ` A ) ) )

  proof
    cA
    cfn
    wcel
    #
    cA
    c0
    wne
    #
    wa
    #
    c1
    cn0
    wcel
    #
    cA
    chash
    cfv
    #
    cn0
    wcel
    #
    c1
    @4
    cle
    wbr
    c1
    cc0
    @4
    cfz
    co
    wcel
    @3
    @2
    1nn0
    a1i
    @0
    @5
    @1
    cA
    hashcl
    adantr
    cA
    cfn
    hashge1
    c1
    @4
    elfz2nn0
    syl3anbrc
end
