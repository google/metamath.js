include "cfv.mm"
include "wcel.mm"
include "cdif.mm"
include "ntrclsnvobr.mm"
include "ntrclselnel1.mm"
include "con2bid.mm"

theorem ntrclselnel2
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
  disjoint I j
  disjoint I k
  disjoint S j
  disjoint i ph
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> ( X e. ( I ` ( B \ S ) ) <-> -. X e. ( K ` S ) ) )

  proof
    wph
    cX
    cS
    cK
    cfv
    wcel
    cX
    cB
    cS
    cdif
    cI
    cfv
    wcel
    wph
    cB
    cD
    cS
    vi
    vj
    vk
    cK
    cI
    cO
    cX
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
    ntrcls.x
    ntrcls.s
    ntrclselnel1
    con2bid
end
