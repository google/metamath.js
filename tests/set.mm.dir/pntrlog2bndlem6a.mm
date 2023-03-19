include "cv.mm"
include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "caddc.mm"
include "cuz.mm"
include "cfz.mm"
include "cun.mm"
include "wceq.mm"
include "cn.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cn0.mm"
include "elioore.mm"
include "adantl.mm"
include "crp.mm"
include "1rp.mm"
include "a1i.mm"
include "rpred.mm"
include "clt.mm"
include "eliooord.mm"
include "simpld.mm"
include "ltled.mm"
include "rpgecld.mm"
include "adantr.mm"
include "rpdivcld.mm"
include "rprege0d.mm"
include "flge0nn0.mm"
include "nn0p1nn.mm"
include "3syl.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "rpge0d.mm"
include "lediv2ad.mm"
include "recnd.mm"
include "div1d.mm"
include "breqtrd.mm"
include "flword2.mm"
include "syl3anc.mm"
include "fzsplit2.mm"
include "syl2anc.mm"

theorem pntrlog2bndlem6a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let vi: setvar i
  let va: setvar a
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  assume pntsval.1: |- S = ( a e. RR |-> sum_ i e. ( 1 ... ( |_ ` a ) ) ( ( Lam ` i ) x. ( ( log ` i ) + ( psi ` ( a / i ) ) ) ) )
  assume pntrlog2bnd.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )
  assume pntrlog2bnd.t: |- T = ( a e. RR |-> if ( a e. RR+ , ( a x. ( log ` a ) ) , 0 ) )
  assume pntrlog2bndlem5.1: |- ( ph -> B e. RR+ )
  assume pntrlog2bndlem5.2: |- ( ph -> A. y e. RR+ ( abs ` ( ( R ` y ) / y ) ) <_ B )
  assume pntrlog2bndlem6.1: |- ( ph -> A e. RR )
  assume pntrlog2bndlem6.2: |- ( ph -> 1 <_ A )

  disjoint a i
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint S x
  disjoint S y
  disjoint R x
  disjoint R y
  disjoint a c
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint c i
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint B n
  disjoint m ph
  disjoint n ph
  disjoint S c
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint R c
  disjoint R m
  disjoint R n
  disjoint T m
  disjoint T n
  assert |- ( ( ph /\ x e. ( 1 (,) +oo ) ) -> ( 1 ... ( |_ ` x ) ) = ( ( 1 ... ( |_ ` ( x / A ) ) ) u. ( ( ( |_ ` ( x / A ) ) + 1 ) ... ( |_ ` x ) ) ) )

  proof
    wph
    vx
    cv
    #
    c1
    cpnf
    cioo
    co
    wcel
    #
    wa
    #
    @0
    cA
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    c1
    cuz
    cfv
    #
    wcel
    @0
    cfl
    cfv
    #
    @4
    cuz
    cfv
    wcel
    #
    c1
    @7
    cfz
    co
    c1
    @4
    cfz
    co
    @5
    @7
    cfz
    co
    cun
    wceq
    @2
    @5
    cn
    @6
    @2
    @3
    cr
    wcel
    #
    cc0
    @3
    cle
    wbr
    wa
    @4
    cn0
    wcel
    @5
    cn
    wcel
    @2
    @3
    @2
    @0
    cA
    @2
    @0
    c1
    @1
    @0
    cr
    wcel
    #
    wph
    @0
    c1
    cpnf
    elioore
    adantl
    #
    c1
    crp
    wcel
    #
    @2
    1rp
    a1i
    #
    @2
    c1
    @0
    @2
    c1
    @13
    rpred
    @11
    @2
    c1
    @0
    clt
    wbr
    #
    @0
    cpnf
    clt
    wbr
    #
    @1
    @14
    @15
    wa
    wph
    @0
    c1
    cpnf
    eliooord
    adantl
    simpld
    ltled
    rpgecld
    #
    wph
    cA
    crp
    wcel
    @1
    wph
    cA
    c1
    pntrlog2bndlem6.1
    @12
    wph
    1rp
    a1i
    pntrlog2bndlem6.2
    rpgecld
    adantr
    #
    rpdivcld
    #
    rprege0d
    @3
    flge0nn0
    @4
    nn0p1nn
    3syl
    nnuz
    syl6eleq
    @2
    @9
    @10
    @3
    @0
    cle
    wbr
    @8
    @2
    @3
    @18
    rpred
    @11
    @2
    @3
    @0
    c1
    cdiv
    co
    @0
    cle
    @2
    c1
    cA
    @0
    @13
    @17
    @11
    @2
    @0
    @16
    rpge0d
    wph
    c1
    cA
    cle
    wbr
    @1
    pntrlog2bndlem6.2
    adantr
    lediv2ad
    @2
    @0
    @2
    @0
    @11
    recnd
    div1d
    breqtrd
    @3
    @0
    flword2
    syl3anc
    @4
    c1
    @7
    fzsplit2
    syl2anc
end
