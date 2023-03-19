include "cdif.mm"
include "wcel.mm"
include "cr.mm"
include "clt.mm"
include "wor.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "crab.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "fzfi.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "mp2an.mm"
include "a1i.mm"
include "ballotlem5.mm"
include "rabn0.mm"
include "sylibr.mm"
include "cn.mm"
include "fz1ssnn.mm"
include "nnssre.mm"
include "sstri.mm"
include "3jca.mm"
include "ltso.mm"
include "jctil.mm"
include "fiinf2g.mm"
include "sseli.mm"
include "anim1i.mm"
include "reximi2.mm"
include "3syl.mm"

theorem ballotlemsup
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  let cP: class P
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cI: class I
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vj: setvar j
  let vd: setvar d
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotth.e: |- E = { c e. O | A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` c ) ` i ) }
  assume ballotth.mgtn: |- N < M
  assume ballotth.i: |- I = ( c e. ( O \ E ) |-> inf ( { k e. ( 1 ... ( M + N ) ) | ( ( F ` c ) ` k ) = 0 } , RR , < ) )

  disjoint c k
  disjoint c y
  disjoint c z
  disjoint k y
  disjoint k z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint F y
  disjoint F z
  disjoint M y
  disjoint M z
  disjoint N y
  disjoint N z
  disjoint k w
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint F w
  disjoint M w
  disjoint N w
  disjoint M c
  disjoint N c
  disjoint O c
  disjoint M i
  disjoint N i
  disjoint O i
  disjoint M k
  disjoint N k
  disjoint O k
  disjoint c i
  disjoint F c
  disjoint F i
  disjoint F k
  disjoint C i
  disjoint i k
  disjoint E i
  disjoint E k
  disjoint C k
  disjoint I k
  disjoint c k
  disjoint E c
  disjoint I i
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint c d
  disjoint d k
  assert |- ( C e. ( O \ E ) -> E. z e. RR ( A. w e. { k e. ( 1 ... ( M + N ) ) | ( ( F ` C ) ` k ) = 0 } -. w < z /\ A. w e. RR ( z < w -> E. y e. { k e. ( 1 ... ( M + N ) ) | ( ( F ` C ) ` k ) = 0 } y < w ) ) )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    cr
    clt
    wor
    #
    vk
    cv
    cC
    cF
    cfv
    cfv
    cc0
    wceq
    #
    vk
    c1
    cM
    cN
    caddc
    co
    #
    cfz
    co
    #
    crab
    #
    cfn
    wcel
    #
    @5
    c0
    wne
    #
    @5
    cr
    wss
    #
    w3a
    #
    wa
    vw
    cv
    #
    vz
    cv
    #
    clt
    wbr
    wn
    vw
    @5
    wral
    @11
    @10
    clt
    wbr
    vy
    cv
    @10
    clt
    wbr
    vy
    @5
    wrex
    wi
    vw
    cr
    wral
    wa
    #
    vz
    @5
    wrex
    @12
    vz
    cr
    wrex
    @0
    @9
    @1
    @0
    @6
    @7
    @8
    @6
    @0
    @4
    cfn
    wcel
    @5
    @4
    wss
    @6
    c1
    @3
    fzfi
    @2
    vk
    @4
    ssrab2
    #
    @4
    @5
    ssfi
    mp2an
    a1i
    @0
    @2
    vk
    @4
    wrex
    @7
    vx
    cC
    cP
    vi
    vk
    cE
    cF
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotlem5
    @2
    vk
    @4
    rabn0
    sylibr
    @8
    @0
    @5
    @4
    cr
    @13
    @4
    cn
    cr
    @3
    fz1ssnn
    nnssre
    sstri
    sstri
    #
    a1i
    3jca
    ltso
    jctil
    vz
    vw
    vy
    cr
    @5
    clt
    fiinf2g
    @12
    @12
    vz
    @5
    cr
    @11
    @5
    wcel
    @11
    cr
    wcel
    @12
    @5
    cr
    @11
    @14
    sseli
    anim1i
    reximi2
    3syl
end
