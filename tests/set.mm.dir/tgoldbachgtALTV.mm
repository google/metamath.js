include "cgbo.mm"
include "codd.mm"
include "dfodd3.mm"
include "df-gbo.mm"
include "ax-tgoldbachgt.mm"

theorem tgoldbachgtALTV
  let vm: setvar m
  let vn: setvar n
  let vz: setvar z
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x

  disjoint m n
  disjoint m z
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint n z
  disjoint n p
  disjoint n q
  disjoint n r
  disjoint p z
  disjoint q z
  disjoint r z
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint k x
  assert |- E. m e. NN ( m <_ ( ; 1 0 ^ ; 2 7 ) /\ A. n e. Odd ( m < n -> n e. GoldbachOdd ) )

  proof
    vz
    vm
    vn
    cgbo
    codd
    vr
    vq
    vp
    vz
    dfodd3
    vz
    vr
    vq
    vp
    df-gbo
    ax-tgoldbachgt
end
