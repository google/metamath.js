include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "wne.mm"
include "eldifsn.mm"
include "neneq.mm"
include "simplbiim.mm"
include "adantr.mm"
include "iffalsed.mm"
include "mpt2eq3ia.mm"

theorem mpt2difsnif
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vi: setvar i
  let vj: setvar j
  let cX: class X


  assert |- ( i e. ( A \ { X } ) , j e. B |-> if ( i = X , C , D ) ) = ( i e. ( A \ { X } ) , j e. B |-> D )

  proof
    vi
    vj
    cA
    cX
    csn
    cdif
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
    cD
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
    wn
    #
    @4
    @3
    @1
    cA
    wcel
    @1
    cX
    wne
    @5
    @1
    cA
    cX
    eldifsn
    @1
    cX
    neneq
    simplbiim
    adantr
    iffalsed
    mpt2eq3ia
end
