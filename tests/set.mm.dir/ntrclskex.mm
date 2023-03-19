include "ntrclsnvobr.mm"
include "ntrclsiex.mm"

theorem ntrclskex
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
  assert |- ( ph -> K e. ( ~P B ^m ~P B ) )

  proof
    wph
    cB
    cD
    vi
    vj
    vk
    cK
    cI
    cO
    ntrcls.o
    ntrcls.d
    wph
    cB
    cD
    vi
    vj
    vk
    cI
    cK
    cO
    ntrcls.o
    ntrcls.d
    ntrcls.r
    ntrclsnvobr
    ntrclsiex
end
