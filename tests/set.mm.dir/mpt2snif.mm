include "csn.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "wcel.mm"
include "wa.mm"
include "elsni.mm"
include "adantr.mm"
include "iftrued.mm"
include "mpt2eq3ia.mm"

theorem mpt2snif
  let cB: class B
  let cC: class C
  let cD: class D
  let vi: setvar i
  let vj: setvar j
  let cX: class X


  assert |- ( i e. { X } , j e. B |-> if ( i = X , C , D ) ) = ( i e. { X } , j e. B |-> C )

  proof
    vi
    vj
    cX
    csn
    #
    cB
    vi
    cv
    #
    cX
    wceq
    #
    cC
    cD
    cif
    cC
    @1
    @0
    wcel
    #
    vj
    cv
    cB
    wcel
    #
    wa
    @2
    cC
    cD
    @3
    @2
    @4
    @1
    cX
    elsni
    adantr
    iftrued
    mpt2eq3ia
end
