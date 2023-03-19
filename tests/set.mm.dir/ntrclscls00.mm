include "cfv.mm"
include "wceq.mm"
include "c0.mm"
include "cdif.mm"
include "ntrclsfv1.mm"
include "fveq1d.mm"
include "cvv.mm"
include "ntrclsbex.mm"
include "ntrclsiex.mm"
include "eqid.mm"
include "cpw.mm"
include "wcel.mm"
include "0elpw.mm"
include "a1i.mm"
include "dssmapfv3d.mm"
include "eqtr3d.mm"
include "dif0.mm"
include "fveq2i.mm"
include "id.mm"
include "syl5eq.mm"
include "difeq2d.mm"
include "difid.mm"
include "syl6eq.mm"
include "sylan9eq.mm"
include "pwidg.mm"
include "syl.mm"
include "ntrclsfv.mm"
include "impbida.mm"

theorem ntrclscls00
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
  disjoint I j
  disjoint I k
  disjoint K j
  disjoint K k
  disjoint i ph
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> ( ( I ` B ) = B <-> ( K ` (/) ) = (/) ) )

  proof
    wph
    cB
    cI
    cfv
    #
    cB
    wceq
    #
    c0
    cK
    cfv
    #
    c0
    wceq
    #
    wph
    @1
    @2
    cB
    cB
    c0
    cdif
    #
    cI
    cfv
    #
    cdif
    #
    c0
    wph
    c0
    cI
    cD
    cfv
    #
    cfv
    #
    @2
    @6
    wph
    c0
    @7
    cK
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
    ntrclsfv1
    fveq1d
    wph
    cB
    cD
    c0
    @8
    vk
    cI
    @7
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
    #
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
    ntrclsiex
    @7
    eqid
    c0
    cB
    cpw
    #
    wcel
    wph
    cB
    0elpw
    a1i
    @8
    eqid
    dssmapfv3d
    eqtr3d
    @1
    @6
    cB
    cB
    cdif
    #
    c0
    @1
    @5
    cB
    cB
    @1
    @5
    @0
    cB
    @4
    cB
    cI
    cB
    dif0
    #
    fveq2i
    @1
    id
    syl5eq
    difeq2d
    cB
    difid
    #
    syl6eq
    sylan9eq
    wph
    @3
    @0
    cB
    @11
    cK
    cfv
    #
    cdif
    #
    cB
    wph
    cB
    cD
    cB
    vi
    vj
    vk
    cI
    cK
    cO
    ntrcls.o
    ntrcls.d
    ntrcls.r
    wph
    cB
    cvv
    wcel
    cB
    @10
    wcel
    @9
    cB
    cvv
    pwidg
    syl
    ntrclsfv
    @3
    @15
    @4
    cB
    @3
    @14
    c0
    cB
    @3
    @14
    @2
    c0
    @11
    c0
    cK
    @13
    fveq2i
    @3
    id
    syl5eq
    difeq2d
    @12
    syl6eq
    sylan9eq
    impbida
end
