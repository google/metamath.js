include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wrex.mm"
include "wn.mm"
include "wa.mm"
include "wbr.mm"
include "adantr.mm"
include "simpr.mm"
include "ntrclsneine0lem.mm"
include "ralbidva.mm"

theorem ntrclsneine0
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cD: class D
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cI: class I
  let cK: class K
  let cO: class O
  let vs: setvar s
  assume ntrcls.o: |- O = ( i e. _V |-> ( k e. ( ~P i ^m ~P i ) |-> ( j e. ~P i |-> ( i \ ( k ` ( i \ j ) ) ) ) ) )
  assume ntrcls.d: |- D = ( O ` B )
  assume ntrcls.r: |- ( ph -> I D K )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B s
  disjoint i j
  disjoint i k
  disjoint i s
  disjoint j k
  disjoint j s
  disjoint k s
  disjoint I j
  disjoint I k
  disjoint I s
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint ph s
  disjoint ph x
  disjoint i x
  disjoint j x
  disjoint k x
  disjoint s x
  assert |- ( ph -> ( A. x e. B E. s e. ~P B x e. ( I ` s ) <-> A. x e. B E. s e. ~P B -. x e. ( K ` s ) ) )

  proof
    wph
    vx
    cv
    #
    vs
    cv
    #
    cI
    cfv
    wcel
    vs
    cB
    cpw
    #
    wrex
    @0
    @1
    cK
    cfv
    wcel
    wn
    vs
    @2
    wrex
    vx
    cB
    wph
    @0
    cB
    wcel
    #
    wa
    cB
    cD
    vi
    vj
    vk
    cI
    cK
    cO
    @0
    vs
    ntrcls.o
    ntrcls.d
    wph
    cI
    cK
    cD
    wbr
    @3
    ntrcls.r
    adantr
    wph
    @3
    simpr
    ntrclsneine0lem
    ralbidva
end
