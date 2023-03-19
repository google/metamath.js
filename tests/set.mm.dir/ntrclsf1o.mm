include "cvv.mm"
include "ntrclsbex.mm"
include "dssmapf1od.mm"

theorem ntrclsf1o
  let wph: wff ph
  let cB: class B
  let cD: class D
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cI: class I
  let cK: class K
  let cO: class O
  assume ntrcls.o: |- O = ( i e. _V |-> ( k e. ( ~P i ^m ~P i ) |-> ( j e. ~P i |-> ( i \ ( k ` ( i \ j ) ) ) ) ) )
  assume ntrcls.d: |- D = ( O ` B )
  assume ntrcls.r: |- ( ph -> I D K )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint i ph
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> D : ( ~P B ^m ~P B ) -1-1-onto-> ( ~P B ^m ~P B ) )

  proof
    wph
    cB
    cD
    vk
    cO
    cvv
    vj
    vi
    ntrcls.o
    ntrcls.d
    wph
    cB
    cD
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsbex
    dssmapf1od
end
