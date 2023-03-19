include "cfv.mm"
include "wcel.mm"
include "cdif.mm"
include "wn.mm"
include "ntrclsfv2.mm"
include "eqcomd.mm"
include "fveq1d.mm"
include "cvv.mm"
include "ntrclsbex.mm"
include "ntrclskex.mm"
include "eqid.mm"
include "dssmapfv3d.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "wa.mm"
include "wb.mm"
include "eldif.mm"
include "a1i.mm"
include "mpbirand.mm"
include "bitrd.mm"

theorem ntrclselnel1
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
  let cX: class X
  assume ntrcls.o: |- O = ( i e. _V |-> ( k e. ( ~P i ^m ~P i ) |-> ( j e. ~P i |-> ( i \ ( k ` ( i \ j ) ) ) ) ) )
  assume ntrcls.d: |- D = ( O ` B )
  assume ntrcls.r: |- ( ph -> I D K )
  assume ntrcls.x: |- ( ph -> X e. B )
  assume ntrcls.s: |- ( ph -> S e. ~P B )

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
  assert |- ( ph -> ( X e. ( I ` S ) <-> -. X e. ( K ` ( B \ S ) ) ) )

  proof
    wph
    cX
    cS
    cI
    cfv
    #
    wcel
    cX
    cB
    cB
    cS
    cdif
    cK
    cfv
    #
    cdif
    #
    wcel
    #
    cX
    @1
    wcel
    wn
    #
    wph
    @0
    @2
    cX
    wph
    @0
    cS
    cK
    cD
    cfv
    #
    cfv
    #
    @2
    wph
    cS
    cI
    @5
    wph
    @5
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
    eqcomd
    fveq1d
    wph
    cB
    cD
    cS
    @6
    vk
    cK
    @5
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
    @5
    eqid
    ntrcls.s
    @6
    eqid
    dssmapfv3d
    eqtrd
    eleq2d
    wph
    @3
    cX
    cB
    wcel
    #
    @4
    ntrcls.x
    @3
    @7
    @4
    wa
    wb
    wph
    cX
    cB
    @1
    eldif
    a1i
    mpbirand
    bitrd
end
