include "cfv.mm"
include "cdif.mm"
include "ntrclsfv2.mm"
include "fveq1d.mm"
include "cvv.mm"
include "ntrclsbex.mm"
include "ntrclskex.mm"
include "eqid.mm"
include "dssmapfv3d.mm"
include "eqtr3d.mm"

theorem ntrclsfv
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cI: class I
  let cK: class K
  let cO: class O
  assume ntrcls.o: |- O = ( i e. _V |-> ( k e. ( ~P i ^m ~P i ) |-> ( j e. ~P i |-> ( i \ ( k ` ( i \ j ) ) ) ) ) )
  assume ntrcls.d: |- D = ( O ` B )
  assume ntrcls.r: |- ( ph -> I D K )
  assume ntrclsfv.s: |- ( ph -> S e. ~P B )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint K j
  disjoint K k
  disjoint S j
  disjoint i ph
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> ( I ` S ) = ( B \ ( K ` ( B \ S ) ) ) )

  proof
    wph
    cS
    cK
    cD
    cfv
    #
    cfv
    #
    cS
    cI
    cfv
    cB
    cB
    cS
    cdif
    cK
    cfv
    cdif
    wph
    cS
    @0
    cI
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
    ntrclsfv2
    fveq1d
    wph
    cB
    cD
    cS
    @1
    vk
    cK
    @0
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
    ntrclskex
    @0
    eqid
    ntrclsfv.s
    @1
    eqid
    dssmapfv3d
    eqtr3d
end
