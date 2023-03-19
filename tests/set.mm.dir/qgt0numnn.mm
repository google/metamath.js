include "cq.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cnumer.mm"
include "cfv.mm"
include "cz.mm"
include "cn.mm"
include "qnumcl.mm"
include "adantr.mm"
include "qnumgt0.mm"
include "biimpa.mm"
include "elnnz.mm"
include "sylanbrc.mm"

theorem qgt0numnn
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A e. QQ /\ 0 < A ) -> ( numer ` A ) e. NN )

  proof
    cA
    cq
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    cA
    cnumer
    cfv
    #
    cz
    wcel
    #
    cc0
    @2
    clt
    wbr
    #
    @2
    cn
    wcel
    @0
    @3
    @1
    cA
    qnumcl
    adantr
    @0
    @1
    @4
    cA
    qnumgt0
    biimpa
    @2
    elnnz
    sylanbrc
end
